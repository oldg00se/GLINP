import getopt
import sys
import time

from complete import completeMain
from generateinit import modifyGenerateInitialState, addInitialState
from generateplan import generateItemPlan
from infskeleton import infskeleton, printOutProg,computeDepthOfProg
# from verifyProgram import  verifyProgram
from verifyPseudoProgram import isPseudo, verifyPseudoProgram

default=3
#the bound of variable
bound=default
#the number of the initial state
stateSize=default
# mode 1 lin2022, mode 2 random
modelSort = 1
# frag 1 pp, frag 2 restricted
frag = 1
# domain
GLINP=''

left=''
right=''

# generate planning program
def generatePlanningProgram(domain):
    global left
    global right
    global bound
    global stateSize
    global modelSort
    probfileSet = []

    width = 17 - len(domain)
    for i in range(int(width / 2)):
        left += ' '
    right = left
    if (len(left) + len(right) + len(domain) != 17):
        right = right + ' '

    print("\n#######################################################")
    print("####################                 ##################")
    print("####################" + left + domain + right + "##################")
    print("####################                 ##################")
    print("#######################################################")

    print("\n------------------------------------------------------")
    print("-------------------Generate Initial States----------------")
    print("------------------------------------------------------")

    root = ''
    if modelSort == 1:
        root = './domain/' + domain
        modifyGenerateInitialState(domain,bound,stateSize,modelSort)
    elif modelSort == 2:
        root = './domain/' + domain + '/Random'
        modifyGenerateInitialState(domain,bound,stateSize,modelSort)

    i = 1
    while i <= stateSize:
        probfileSet.append(root + '/prob' + str(i) + '.pddl')
        i = i + 1

    # print(probfileSet)

    print("\n------------------------------------------------------")
    print("---------------------Generate Plans----------------")
    print("------------------------------------------------------")

    ItemPlan, plans, actionToLetterList, letterToActionList = generateItemPlan(domain,probfileSet)

    print("\n------------------------------------------------------")
    print("---------------------InfSkeleton----------------")
    print("------------------------------------------------------")

    GenProgram= infskeleton(ItemPlan, actionToLetterList, letterToActionList)


    print("\n------------------------------------------------------")
    print("---------------------Complete----------------")
    print("------------------------------------------------------")

    domainfile = './domain/' + domain + '/domain.pddl'

    GenProgram,actionList,proList,numList,initPro = completeMain(GenProgram,domainfile,probfileSet,plans,actionToLetterList, letterToActionList)

    print("\n2. The generated Planning Program as follow:")
    program,length=printOutProg(GenProgram,0)
    depth=computeDepthOfProg(GenProgram,0)
    print(program,"\n")
    print("The length of Planning Program is:{}".format(length))
    print("The depth of Planning Program is:{}".format(depth))


    return GenProgram,actionList,proList,numList,initPro

# generate the planning program
def GenerateGLINP(domain):
    print("\n------------------------------------------------------")
    # verify restricted planning program
    e1 = time.time()
    GenCode, actionList, proList, numList, initPro = generatePlanningProgram(domain)
    e2 = time.time()
    print('Generation Time: %fs' % (e2 - e1))

    res_isPseudo=[]
    for i in range(len(initPro)):
        # print("\n++++++++++++++++++",i,"+++++++++++++++++++++")
        # print(initPro[i])
        loopflag=False
        res_isPseudo.append(isPseudo(GenCode, actionList, proList, numList,initPro[i],loopflag))


    # print("res_isPseudo:",res_isPseudo)
    re=True
    for i in range(len(res_isPseudo)):
        re = re and res_isPseudo[i]
    if re == True:
        print("\n------------------------------------------------------")
        print('The program is PP.')
        print("\n------------------------------------------------------")

        res, states = verifyPseudoProgram(domain, GenCode, actionList, proList, numList)

        if res == False:
            print("\n------------------------------------------------------")
            print('The program is not correct')
            print("\n------------------------------------------------------")
            print(states)
    else:
        print("\n------------------------------------------------------")
        print('The program is not PP.')
        print("\n------------------------------------------------------")
    print()
    print("#######################################################")
    print("##################                  ###################")
    print("##################        END       ###################")
    print("##################                  ###################")
    print("#######################################################")

if __name__ == "__main__":
    try:
        options, args = getopt.getopt(sys.argv[1:], "d:p:b:n:m:f:", ["domain", "planner", "bound", "number","model","fragment"])
        for option, value in options:
            if option in ("-d", "--domain"):
                GLINP = value
            if option in ("-b", "--bound"):
                bound = int(value)
            if option in ("-n", "--number"):
                stateSize = int(value)
            if option in ("-m", "--model"):
                modelSort = int(value)
    except:
        print("#############################################################################")
        print("Incorrect run command.")
        print("Please recheck the run command.")
        print("Exit the synthesis of the program")
        print("#############################################################################")
        sys.exit()
    GenerateGLINP(GLINP)

#### command
###  python3 main.py -b 3 -n 3 -d Chop
