'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
*                           PISIS FIME UANL                                    *
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
* Program Name:      : A DESCOMPOSITION METHOD BASED IN COLUMN GENERATION      *
* Description        : THIS PROGRAM IS FOR EVALUATING THE PERFOMANCE OF A      *
                       PARALLEL SOLVE OF PRICING PROBLEM WITH DIFERENT         *
                       NUMBER OF CORES                                         *
* Functional         : Nelly Monserrat Hernandez Gonzalez                      *
* Programmer         : Nelly Monserrat Hernandez Gonzalez                      *
* Creation date      : 23/11/2015                                              *
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''

#&======================================================================
#& Importing modules
#&======================================================================
import cplex
from time import time
from cplex.exceptions import CplexSolverError
from os import remove
from sys import argv
from random import randint, seed
from math import ceil, sqrt
from multiprocessing import Pool, cpu_count, Manager, freeze_support
#pylint: disable=line-too-long
#pylint: disable=invalid-name
#pylint: disable=maybe-no-member
#pylint: disable=pointless-string-statement

#&======================================================================
#& Global varaibles
#&======================================================================
## Cardinality of:
I = 5  ## PLANTS
J = 7  ## DC
K = int(argv[1])  ## RETAILERS
#&Parameters of the problem
H = 50
LAMDA = 360
TETHA, BETA = 1, 1
ZA, ZG = 0.67, -0.8416
ZE = ZA - ZG
TAU = sqrt(2 * LAMDA /(TETHA * H))
FI = TETHA * H *LAMDA * ZA
BP = BETA * LAMDA
ETA = sqrt(2 * TETHA * H *LAMDA)
##Lists for each element in the problem
DCS, PLANTS, RETAILERS = [], [], []
##Auxiliary parameters
TOTAL_DEMAND, TOTAL_VARIANCE = 0, 0
MINIMUN_DEMAND, MV = 0, 0
COLUMNS, SETS = list(), list()
LINE_APROX_MV = 0
SOLUTION_MASTER = list()

'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
*************** Defining retailers, centers and plants as classes***************
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
class Client:
    '''Define client'''
    def __init__(self, name):
        self.name = str(name)
        self.mean = randint(15, 80)
        self.variance = randint(40, 80)
    def __cmp__(self, other):
        try:
            if self.mean == other.mean: ## if there're retailers with the same mean
                return cmp(self.name, other.name) ##they'll be order lexicographically
            return self.mean - other.mean
        except:
            return -1 ##if the instance has incorrect information
    def __str__(self): ##the way to print instances
        return '%s: %d,%d' % (self.name, self.mean, self.variance)
        #return 'N%s: %d' % (self.name, self.mean)
    def __repr__(self):
        return self.__str__()
    def __eq__(self, other): #equality
        return self.name == other.name
    def __hash__(self): #unique id for sets and dictionaries
        return hash(self.name)
    def __radd__(self, acum): #acumulated sum
        return acum + self.mean
class CD:
    '''Define distribution center'''
    def __init__(self, name, demand):
        self.name = str(name)
        self.capCD = generate_values(demand * 2, TOTAL_DEMAND * 5)
        self.ctol = ceil(0.2 * self.capCD)
        self.ctoo = randint(50, 130)
        self.ctot = [randint(10, 30) for k in xrange(K)]
    def __str__(self):
        #return '%s:%d' % (self.name, self.capCD)
        return '%s:%s' % (self.name, self.ctot[:])
    def __repr__(self):
        return self.__str__()
    def __radd__(self, acum):
        return acum + self.capCD
    def increase(self):
        '''for feasibility'''
        self.capCD *= 2
class Plant:
    '''Define plant'''
    def __init__(self, name):
        self.name = str(name)
        self.production = generate_values(int(2 * TOTAL_DEMAND /I), TOTAL_DEMAND)
        self.g = [randint(50, 100) for i in xrange(J)]
        self.a = [randint(10, 70) for i in xrange(J)]
        self.l = [randint(7, 20) for i in xrange(J)]
    def __str__(self):
        return '%s:%d' % (self.name, self.production)
    def __repr__(self):
        return self.__str__()
    def __radd__(self, acum):
        return acum + self.production
    def increase(self):
        self.production *= 2  #for feasibility

'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
**************** Classes for being used in pricing problem *********************
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
class New_solution:
    '''Save the candidate column with the parameters'''
    def __init__(self, data):
        '''data has [mean, variance], name, DC, plant and quality, cost'''
        self.information = data
        self.quality = data[4]
    def __str__(self):
        #return str(self.information)
        if len(self.information) > 1:
            return str(self.quality)
    def __repr__(self):
        return self.__str__()
    def __getitem__(self,i):
        return self.information[i]

class Allnew:
    ''' threshold: parameter for filtering solution'''
    def __init__(self, threshold):
        self.position = 0
        self.capacitance = 20 #number of desirable columns
        self.listing = [None] * self.capacitance #list of the best columns
        self.threshold = threshold
        self.counter = 0
    def save(self, aspirant):
        self.counter += 1
        '''To save the best columns '''
        if self.position >= self.capacitance:
            self.position = self.capacitance / 2
            self.listing.sort(key=lambda k: k.quality)
            self.threshold = self.listing[self.position].quality
            for p in xrange(self.position + 1, self.capacitance):
                #eliminate the half of list
                self.listing[p] = None
            self.position += 1
        if aspirant.quality < self.threshold:
            self.listing[self.position] = aspirant
            self.position += 1
            return True
        return False
    def __str__(self):
        s = '[%d] ' % self.threshold
        for p in xrange(self.position):
            self.listing[p]
            s += '%s ' % self.listing[p]
        return s
    def __repr__(self):
        return self.str()

''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
'''**************************** Generate inputs *****************************'''
''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
def timing(f):
    '''keep track of the time'''
    def wrap(*args):
        '''getting time elapsed'''
        start = time()
        ret = f(*args)
        duration = time()-start
        print K, '%s %0.3f' % (argv[2],duration*1000.0)
        elapsed.append(duration*1000.0)
        return ret
    return wrap

#@profile
def create_elements():
    '''RETAILERS, DCS, PLANTS are created'''
    global RETAILERS, DCS, PLANTS
    global MINIMUN_DEMAND, TOTAL_DEMAND
    global TOTAL_VARIANCE
    RETAILERS = [Client(k+1) for k in xrange(K)]
    maximum_demand = max(RETAILERS).mean
    minimum_variance = min(RETAILERS[k].variance for k in xrange(K))
    TOTAL_DEMAND = sum(RETAILERS)
    DCS = [CD(j+1, maximum_demand) for j in xrange(J)]
    PLANTS = [Plant(i+1) for i in xrange(I)]
    MINIMUN_DEMAND = min(RETAILERS).mean
    TOTAL_VARIANCE = sum(RETAILERS[i].variance for i in xrange(K))
    ##Assert storage capacity
    check_feasibility(DCS, 4)
    check_feasibility(PLANTS, 1)

def generate_values(lower, upper):
    '''define lower and upper limit'''
    return randint(lower, upper) if lower < upper else randint(upper, lower)

def remove_files():
    'For removing files of the models'
    try:
        remove("/Dropbox/0_Descomposition/.lp")
        remove("/Dropbox/0_Descomposition/master.lp")
    except:
        pass

#@profile
def check_feasibility(facility, size):
    '''Check capacity, and adjust it in DC and Plants if needs be'''
    capacity = sum(facility)
    while capacity < (TOTAL_DEMAND * size * J):
        for component in facility:
            component.increase()
        capacity = sum(facility)

'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
**************** Creating the model with all assigments ************************
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
def test(b, k):
    'For knowing which retailer is in the subset b'
    return int((b & (1<<k)) > 0)

def members(name, facility, specific):
    'Verify if facility "specific" is in the group "name"'
    'name has the formmat E_b_i_j'
    separate = list()
    separate = name.split('_')
    if facility == "R":
        #Get the group and assert if retailer is in there
        return (int(separate[1]) & (1<<specific)) > 0
    else:
        index = 2 if facility == "I" else 3
        return int(separate[index]) == specific

def create_group(b):
    '''Calculating parameters for the subsets'''
    trait = list()
    parameterSub = get_group(b)
    meanSub = parameterSub[0]
    varianceSub = parameterSub[1]
    for j in xrange(J):
        safetyStockMax = parameterSub[2][j]
        for plant in PLANTS:
            w1 = sqrt(meanSub*(DCS[j].ctoo + BETA * plant.g[j]))
            w2 = sqrt(varianceSub * plant.l[j])
            ocupation = ceil(TAU * w1 + ZE * w2)
            if ocupation <= DCS[j].capCD:
                costs = BP * safetyStockMax + FI * w2 + ETA * w1
                iD = "E_"+str(b)+"_"+plant.name+"_"+str(j + 1)
                trait.append((iD, ocupation, meanSub, costs))
    return trait

#@profile
def get_group(subset, elements=None, dualesPi=None):
    'Calculating subset parameters'
    #Subset paramerters (mean, variance, transpotation cost (J), dual variables)
    if elements == None:
        r = RETAILERS
        d = DCS
        parameterSub = [0, 0, [0]*J]
    else:
        r = elements[0]
        d = elements[1]
        parameterSub = [0, 0, [0]*J, 0]
    for k in xrange(K):
        if test(subset, k):
            mean_demand = r[k].mean
            parameterSub[0] += mean_demand
            parameterSub[1] += r[k].variance
            if dualesPi is not None:
                parameterSub[3] += dualesPi[k] #Pi_k * Y_k_j
            for j in xrange(J):
                parameterSub[2][j] += mean_demand * d[j].ctot[k]
    return parameterSub

'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
**************************** Optimization **************************************
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
#@profile
def setting_model():
    '''Call cplex '''
    model = cplex.Cplex()
    model.objective.set_sense(model.objective.sense.minimize)
    # Turn off the presolve reductions & set primal simplex method.
    model.parameters.preprocessing.reduce.set(0)
    model.parameters.lpmethod.set(model.parameters.lpmethod.values.primal)
    model.set_results_stream(None) #don display
    model.set_log_stream(None)
    model.set_error_stream(None)
    model.set_warning_stream(None)
    return model

#@profile
def optimize(model):
    '''the lp file just considering the variables with coefficient equal to 1'''
    try:
        model.solve()
    except CplexSolverError, e:
        print "Exception raised during solve: " + e
    else:
        ms = model.solution
        if ms.get_status() == 1 or 101 or 102:
            #print '1,', ms.get_objective_value()
            b = model.variables.get_num()
            base = [(model.variables.get_names(j), model.solution.get_values(j)) for j in xrange(b) if ms.get_values(j) != 0]
            return base
        else:
            pass

'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
*************************** Descomposition *************************************
================================================================================
*************************** Master problem *************************************
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
#@profile
def master():
    '''Master model'''
    b = len(COLUMNS)
    LIP = setting_model()
    #cplex.clearModel()
    LIP =setting_model()
    aC = LIP.linear_constraints.add #add constraint to the model LIP
    aV = LIP.variables.add #add variables
    aV(names=[COLUMNS[s][5] for s in xrange(b)], \
            obj=[COLUMNS[s][4] for s in xrange(b)], lb=[0] * b, ub=[1] * b)
    aV(names=["x_"+str(j+1) for j in xrange(J)], \
            obj=[DCS[j].ctol for j in xrange(J)], lb=[0]*J, ub=[1]*J)
    for k in xrange(K):
        ind = [ebij[5] for ebij in COLUMNS if ebij[0][k] == 1]
        val = [1]*len(ind)
        row = [[ind, val]]
        aC(lin_expr=row, senses=["E"], rhs=[1])
    for i in xrange(I):
        constraint = [ebij[5:7] for ebij in COLUMNS if int(ebij[1]) == i+1]
        b = len(constraint)
        ind = [constraint[s][0] for s in xrange(b)]
        val = [constraint[s][1] for s in xrange(b)]
        row = [[ind, val]]
        aC(lin_expr=row, senses=["L"], rhs=[PLANTS[i].production])
    for j in xrange(J):
        constraint = [ebij[3:6] for ebij in COLUMNS if ebij[2] == j+1]
        b = len(constraint)
        ind = [constraint[s][2] for s in xrange(b)]+["x_" +str(j+1)]
        val = [constraint[s][0] for s in xrange(b)]+[- DCS[j].capCD]
        row = [[ind, val]]
        aC(lin_expr=row, senses=["L"], rhs=[0])
    for v in optimize(LIP):
        base = v[0].split('_')
        '''
        if base[0] == "E":
            #print plant, DC, associated retailers, variable value
            print base[2:4], simplifying(base[1]), v[1]
        else:
            print 'DC: ', base[1], v[1]
        '''
    return LIP.solution.get_dual_values()
    LIP.write("master.lp")

#@profile
def first_columns(size_input):
    '''The input is the number of desable subsets'''
    b = 0 #counter of subsets
    parameterSub = {}    ##Paramerters for each subset (mean and variance)
    dkb = {} ##Adjacency list(retailers in subset b)
    while b < size_input:
        ## Partition is the number of groups for creating
        ## without considering the singleton not the set of all the retailers
        partitions = randint(2, J - 1)
        for j in xrange(1, J):
            parameterSub[j] = [0, 0]
            dkb[j] = [] #clean the adjacency vector
        for client in RETAILERS:
            ## each client is assigned to a partition
            selection = randint(1, partitions)
            for j in xrange(1, partitions + 1):
                #creating the adjacency vector of the partition
                dkb[j].append(int(j == selection))
            parameterSub[selection][0] += client.mean
            parameterSub[selection][1] += client.variance
        for s in xrange(1, partitions + 1):
        #Each formed group is evaluating, if it is not null it is
        #assigned to each plant & DC
            if parameterSub[s][0] > 0:
                b += 1
                SETS.append(dkb[s])
                create_column(b, dkb[s], parameterSub[s])
#@profile
def create_column(b, dkb, parameterSub):
    '''Calculating parameters for the subsets'''
    meanSub = parameterSub[0]
    varianceSub = parameterSub[1]
    for j in xrange(J):
        safetyStockMax = sum(dkb[k]*RETAILERS[k].mean*DCS[j].ctot[k]\
                             for k in xrange(K))
        for plant in PLANTS:
            w1 = sqrt(meanSub*(DCS[j].ctoo + BETA * plant.g[j]))
            w2 = sqrt(varianceSub * plant.l[j])
            occupation = ceil(TAU * w1 + ZE * w2)
            if occupation <= DCS[j].capCD:
                costs = BP * safetyStockMax + FI * w2 + ETA * w1
                nombre = "E_"+str(b)+"_"+plant.name+"_"+str(j + 1)
                COLUMNS.append([dkb, plant.name, j + 1, occupation, \
                            costs, nombre, meanSub])

def simplifying(b):
    '''Get the retailers in the subset b'''
    return [k+1 for k in xrange(K) if SETS[int(b)-1][k] == 1]

'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
*************************** pricing problem ************************************
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
def coordinator(fuente):
    sumidero = Allnew(0)
    operate = True # if there is elements to process
    while operate:
        answer = None # at he beginnig there is not a answer
        try:
            answer = fuente.get(False) #take the next out for processing
        except:
            pass # no more outputs
        if answer is not None:
            if answer == 'ok': # Have the workers ended?
                operate = False # finish the process
            else: # process the output
                sumidero.save(New_solution(answer))
                #print 'sumidero', sumidero
    return sumidero


#@profile
def work(name, elements, dual, s):
    '''Here is evaluated each possible assigment, and return just the best'''
    contador = 0
    parameterSub = get_group(name, elements[0:2], dual[:K])
    # In parameterSub, [0]: Mean, [1]: Variance, Annual transportation cost
    for j in xrange(J):
        dY = parameterSub[2][j] * BP
        index = 0 #dual value's index
        for plant in elements[2]:
            P_i_j = sqrt(parameterSub[0]*(elements[1][j].ctoo + BETA * plant.g[j]))
            V_i_j = sqrt(parameterSub[1] * plant.l[j])
            occupation = ceil(TAU * P_i_j + ZE * V_i_j)
            if occupation <= elements[1][j].capCD:
                #W_i_j -  #PI_k *  Y_k_j - gamma * S_i_j - sigma * D_i_j
                W_i_j = dY + FI * V_i_j + ETA * P_i_j
                reduce_cost =  W_i_j \
                -parameterSub[3]
                -dual[K + I +j]*(TAU * P_i_j + ZE * V_i_j) \
                -dual[K + index]*parameterSub[0]
                if reduce_cost < 0:
                    contador += 1
                    s.put((parameterSub[0:2], name, j+1, index+1, reduce_cost, W_i_j, occupation))
                    ### the queue is in the manager, does not need return
            index += 1
    return contador

#@profile
@timing
def pricing(dual):
    cpus = cpu_count() - int(argv[2])
    '''process for getting new columns'''
    final = pow(2, K)
    if K < 23:
        section = final
    else:
        section = 100 * cpus # probar valores
    to = 0
    since = 1
    manager = Manager()
    elements = manager.list([RETAILERS, DCS, PLANTS])
    out = manager.Queue() # queue with the result from each worker
    while to < final:
        p = Pool(cpus)
        to = min(since + section, final)
        boss = p.apply_async(coordinator, (out,))
        workers = [p.apply_async(work, (k, elements, dual, out))  for k in xrange(since, to)]
        enviados = 0
        for w in workers:
            enviados += w.get()
        out.put('ok')
        a = boss.get()
        assert a.counter == enviados
        since = to + 1
        p.terminate()
    return a

'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''
*************************** Main ***********************************************
'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''

if __name__ == '__main__':
    freeze_support()
    elapsed = list()
    number_columns = ceil(pow(2, K) * 0.3)
    create_elements()
    first_columns(number_columns)
    multiplier = master()
    a = pricing(multiplier).listing
