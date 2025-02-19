from z3 import *

# check whether program is a pseudo primitive program
from util import generateZ3Variable, getCoff, uncondAct2Logic, getLinearTermInCondition, verifyTEAndG
from datastructure import *
from collections import ChainMap

from z3 import *

# check whether program is a pseudo primitive program
from util import generateZ3Variable, getCoff, uncondAct2Logic, getLinearTermInCondition, verifyTEAndG,find_variable_in_expr,extract_var_name,is_acyclic


def isPseudo(GenCode, actionList, proList, numList,initPro,loopflag):
    if GenCode is None:
        return True

    # no choice
    # if GenCode.flag == 'IF' or GenCode.flag == 'IFe':  # if-else
    #     print("PP contains IF")
    #     return False
    # PP无分支结构
    if GenCode.flag == 'Branch':  # if-else     
        print("PP contains IF")
        return False
        # return True

    # seq
    elif GenCode.flag == 'Seq':  #seq
        fir = GenCode.firstActions
        firDet = True
        if type(fir) == str:
            act = actionList[fir]
            if len(act.subAction) != 0:
                print("PP contains conditional effect")
                return False
            else:
                # 记录不在循环体内的动作对命题变量的effect
                if not(loopflag):
                    for pp in act.effect_pos:
                        initPro[pp] = True

                    for pn in act.effect_neg:
                        initPro[pn] = False
        else:
            firDet = isPseudo(fir,actionList,proList,numList,initPro,loopflag)

        sec = GenCode.secondActions
        secDet = True
        if type(sec) == str:
            act = actionList[sec]
            if len(act.subAction) != 0:
                print("PP contains conditional effect")
                return False
            else:
                if not(loopflag):
                    for pp in act.effect_pos:
                        initPro[pp] = True

                    for pn in act.effect_neg:
                        initPro[pn] = False
        else:
            secDet = isPseudo(sec,actionList,proList,numList,initPro,loopflag)
        
        return firDet and secDet

    # loop 
    elif GenCode.flag == 'Loop':
        loopflag=True

        initPro_preloop = initPro
        # check the loop body
        fir = GenCode.firstActions
        firDet = True
        if type(fir) == str:
            # no selective action
            act = actionList[fir]
            if len(act.subAction) != 0:
                print("PP contains conditional effect")
                return False
        else:
            # nested loop
            print("PP contains nested loop")
            return False

        sec = GenCode.secondActions
        secDet = True
        if type(sec) == str:
            act = actionList[sec]
            if len(act.subAction) != 0:
                print("PP contains conditional effect")
                return False
        else:
            secDet = isPseudo(sec, actionList, proList, numList,initPro,loopflag)
        
        # 循环内的动作已排除，恢复为False
        loopflag = False
        #loop body
        if (firDet and secDet) == False:  
            return False

        # 排除一部分非线性while条件
        elif GenCode.condition == 'False' or GenCode.condition == 'True':
            print("Loop condition %s is not sat" % GenCode.strcondition)
            return False


        # 排除一部分非线性while条件
        elif GenCode.condition.count('And') > 0 or GenCode.condition.count(
                'Or') > 0 or GenCode.condition.count('not') > 0:
            print("Loop condition %s is not sat" %GenCode.strcondition)
            return False

        # 判断条件是否线性，是否-1，num是否incremental。pro是否不变，
        else:
            fir = GenCode.firstActions
      
            preproV, postproV, prenumV, postnumV = generateZ3Variable(proList, numList, 'i', 'o')

            subSeqAxioms1, loopBodyproEff1, loopBodynumEff2 = pseudoProgram2Logic(fir, actionList, proList,numList,
                                                                               preproV, prenumV)


            sec = GenCode.secondActions

            subSeqAxioms2, loopBodyproEff, loopBodynumEff = pseudoProgram2Logic(sec, actionList, proList, numList,
                                                                                loopBodyproEff1, loopBodynumEff2)
           
           
            # print("\n--------------------------------------------")
            # print("subSeqAxioms2:",subSeqAxioms2)
            # print("loopBodyproEff:",loopBodyproEff)
            # print("preproV:",preproV)
            # print("loopBodynumEff:",loopBodynumEff)
            # print("--------------------------------------------\n")
        
            # static
            for k,v in initPro_preloop.items():
                if v == 0:
                    initPro_preloop[k]=False
                else:
                    initPro_preloop[k]=True

            judge = False
            pro_hasEff =[] 
            for k,v in loopBodyproEff.items():
                for p,q in preproV.items():
                    if str(k)==str(p):
                        # print("loopBodyproEff,preproV:"," (",k,p,") - (",v,q,")")
                        if str(v)!=str(q):
                            pro_hasEff.append(k)
                            judge = True
            # print(judge)
            # print("\n------------------------------------------")
            if judge:
                for item in pro_hasEff:
                    # static
                    v=loopBodyproEff[item]
                    q=initPro_preloop[item]
                    # print("loopBodyproEff,initPro_preloop:"," (",item,") - (",v,q,")")
                    if str(v)!=str(q):
                        print("Loop body prop %s is not static" %k)
                        return False

            loopEff = {} 
            condition = GenCode.condition

            for p in proList:
                if p in condition:
                    print("Loop condition %s  contain prop" %condition)
                    return False

            numIncond = []

            for n in numList:
                if n in condition:
                    numIncond.append(n)

            effInloop = {}
            # print("loopBodynumEff:",loopBodynumEff)
            # print("prenumV:",prenumV)
            for n in numList:

                loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])
                # print(n,":",loopEff[n])

                if is_int_value(loopEff[n]) == False:
                    print("Loop body numeric vars %s are not c-incremental" %n)
                    return False

                if n in numIncond:
                    if loopEff[n] == 1 or loopEff[n] == -1:
                        effInloop[n] = loopEff[n]

            if len(effInloop) != 1:
                print("Loop body more than one w in condition")
                return False

            var = list(effInloop.keys())[0]  # get the effect modify value

            # print('-----------------------')
            # print(condition)
            # for n in numIncond:
            #     co = getCoff(n, condition)
            #     print(f'{n}:  {co}')
            # print('----------------------')

            coff = getCoff(var, condition)
            if (abs(coff) == 1):
                # print("Cw's coff in loop condition  is sat")
                return True
            else:
                print("Cw's coff in loop condition  is not sat")
                return False

    else:
        print('incorrect input sort')
        return False

# translate pseudo primitive program to logic formulas
def pseudoProgram2Logic(GenCode, actionList, proList, numList, preproV, prenumV):
    axioms = []
    proEff = copy.deepcopy(preproV)
    numEff = copy.deepcopy(prenumV)

    # print('\n-------------------pseudoProgram2Logic--------------------------')
    # print("preproV",preproV)
    # # print(postproV)
    # print("prenumV",prenumV)
    # # print(postnumV)
    # print("proEff",proEff)
    # print("numEff",numEff)
    # print('---------------------------------------------\n')

    if GenCode is None:
        return axioms, proEff, numEff

    elif type(GenCode) == str:
        # print("str")
        act = actionList[GenCode]
        # print("act:",act.__dict__,"\n")
        # print("act.preFormu:",*act.preFormu)
        axioms, proEff, numEff = uncondAct2Logic(act, proList, numList, preproV, prenumV)
        # print("\n***************************************************")
        # print("str axioms:\n",axioms,"\nstr proEff:\n",proEff,"\nstr numEff\n",numEff)
        # print("***************************************************\n")  


    else:
        if GenCode.flag == 'Seq':
            # print("seq")
            fir = GenCode.firstActions
            subAxioms, subProEff, subNumEff = pseudoProgram2Logic(fir, actionList, proList, numList, preproV, prenumV)
            axioms += subAxioms
            
            sec = GenCode.secondActions
            subAxioms, proEff, numEff = pseudoProgram2Logic(sec, actionList, proList, numList, subProEff, subNumEff)
            axioms += subAxioms

        if GenCode.flag == 'Loop':
            # print("loop")
            subSeqAxioms = []
            fir = GenCode.firstActions
    
            preproV, postproV, prenumV, postnumV = generateZ3Variable(proList, numList, 'i', 'o')
            subSeqAxioms1, loopBodyproEff1, loopBodynumEff2 = pseudoProgram2Logic(fir, actionList, proList, numList,
                                                                                  preproV, prenumV)

            sec = GenCode.secondActions
            subSeqAxioms2, loopBodyproEff, loopBodynumEff= pseudoProgram2Logic(sec, actionList, proList, numList,
                                                                                loopBodyproEff1, loopBodynumEff2)

            subSeqAxioms += subSeqAxioms1
            subSeqAxioms += subSeqAxioms2
            # print('coooocoocococococoooc')
            # # print(subSeqAxioms)
            # # print(loopBodynumEff)
            # print("loopBodyproEff",loopBodyproEff)
            # print('cocococococococococo')

            # cope with precondition
            t = Int('k')
            T = ''
            cond = GenCode.condition
            condt = GenCode.condition

            # get vars in condition
            numIncond = []
            changeNum = ''
            for n in numList:
                if n in cond:
                    numIncond.append(n)

            # get linear term e
            cond = getLinearTermInCondition(cond, numList)
            for k, v in numEff.items():
                cond = cond.replace(k, 'numEff["' + k + '"]')
            e = eval(cond)
            # print("\n!!!!!!!!!!!!!!!!!!!!")
            # print(e)
            # print(simplify(-(e)))
            # print(type(e))
            # print("!!!!!!!!!!!!!!!!!!!!\n")


            # 循环体递增递减值 variable: int  i.e. x : 1  or -1 or 0
            loopEff = {}
            # print("loopBodynumEff:",loopBodynumEff)
            # print("prenumV:",prenumV)

            for n in numList:
                loopEff[n] = simplify(loopBodynumEff[n] - prenumV[n])
            # print("loopEff:",loopEff)
            # get N=e or N = -e
            for n in numIncond:
                if loopEff[n] == 1:
                    changeNum = n
                    coff = getCoff(n, condt)
                    if coff == 1:
                        T = simplify(-(e))
                    elif coff == -1:
                        T = simplify(e)
                if loopEff[n] == -1:
                    changeNum = n
                    coff = getCoff(n, condt)
                    if coff == 1:
                        T = simplify(e)
                    elif coff == -1:
                        T = simplify(-(e))
            # print('N: ', T)

            # print('------loopefff------------')
            # print(loopEff)
            # print('------loopefff------------')
            # +K
            inloopEff = {}
            nloopEff = {}

            for n in numEff:
                if not loopEff[n].__eq__(0):
                    inloopEff[n] = simplify(numEff[n] + t * loopEff[n])
                    nloopEff[n] = numEff[n] + T * loopEff[n]
                else:
                    inloopEff[n] = numEff[n]
                    nloopEff[n] = numEff[n]
                eff = simplify(nloopEff[n] - prenumV[n])
                if not eff.__eq__(0):
                    nloopEff[n] = prenumV[n] + eff
                else:
                    nloopEff[n] = prenumV[n]

            # print("################")
            # print(nloopEff)
            # 循环条件的变量替换
            for n in numList:
                condt = condt.replace(n, 'inloopEff["' + n + '"]')

            # condt = substitute(condt,(prenumV[changeNum], numEff[changeNum]))
            condt = eval(condt)
            condt = simplify(condt)

            # 循环体的前提的变量替换
            subSeqAxiom = simplify(And(subSeqAxioms))
            for n in numList:
                subSeqAxiom = substitute(subSeqAxiom, (prenumV[n], inloopEff[n]))
                        

            for p in proList:
                subSeqAxiom = substitute(subSeqAxiom, (preproV[p], Not(Not(proEff[p]))))
            # print("subSeqAxiom:",subSeqAxiom)

            # 生成公理
            loopsubAxiom = And(T >= 0, ForAll(t, Implies(And(0 <= t, t < T), simplify(And(subSeqAxiom, condt)))))

            axioms.append(loopsubAxiom)

            # print('+++++++++++++++++++++')
            # print(numEff)
            # print('++++++++++++++++++=')

            # 生成最后的proEff(不变) numEff
            for n in numList:
                numEff[n] = nloopEff[n]

            # print('--------------numefff-------------')
            # print(nloopEff)
            # print(numEff)
            # print('--------------numefff-------------')
    # print('------------------pseudoProgram2Logic---------------------------\n')
    
    return axioms, proEff, numEff


# verify pseudo primitive program
def verifyPseudoProgram(domain, GenCode, actionList, proList, numList):
    propInitZ3, propGoalZ3, numInitZ3, numGoalZ3 = generateZ3Variable(proList, numList, 'i', 'g')
    axioms, proEff, numEff = pseudoProgram2Logic(GenCode, actionList, proList, numList, propInitZ3, numInitZ3)
    
    # print("3")
    # print(axioms)
    for p in proList:
        axioms.append(simplify(propGoalZ3[p] == proEff[p]))

    # print("4")
    # print(axioms)
    for n in numList:
        axioms.append(simplify(numGoalZ3[n] == numEff[n]))
    # print("5")
    # print(axioms)

    print(axioms)
    axiom = simplify(And(axioms))
    # print("6")


    return verifyTEAndG(domain, axiom, propInitZ3, numInitZ3, propGoalZ3, numGoalZ3)
