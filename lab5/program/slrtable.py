from grammar import *

DOT = "."
EPSILON = "#"
NOTHING = "NOTHING"
SPEC_TOKEN = "@"

def set_to_vect(s):
    res = list(s)
    return res

def slice(v, m: int, n: int):
    first = v[m:n + 1]
    return first

def str_to_vect(string: str):
    ans = string.split()
    return ans



class SLRTable:
    class Comp:
        def __call__(self, lhs: str, rhs: str) -> bool:
            if lhs[-1] == "'":
                return True
            if rhs[-1] == "'":
                return False
            return lhs < rhs
   
    def is_belong(this,rule:ExtendedRule,arr):
        for elem in arr:
            if rule == elem:
                return True
        return False
    def PrintTable(this):
        print("\t", end="")
        for col in this.cols:
            print(col, end="\t\t")
        print()
        for i in range(len(this.table)):
            for j in range(len(this.table[i])):
                if j == 0:
                    print(f"{i}\t{this.table[i][j]}\t\t", end="")
                else:
                    print(f"{this.table[i][j]}\t\t", end="")
            print()


    def GoTo(this,state:int,token:str):
        element_iter = this.GOTOStateDict.get((state, token))
        if element_iter is None:
            return -1
        return element_iter

    def GetActions(this,state,token):
        terms = this.input_grammar.Terms()
        if token not in terms and token != SPEC_TOKEN:
            return Actions()

        ind = this.cols.index(token)
        actionsString = this.table[state][ind]

        if actionsString == "acc":
            ans = Actions()
            ans.is_acc = True
            return ans

        shiftActions = []
        reduceActions = []

        ss = actionsString.split()
        for action in ss:
            if action[0] == 'S':
                shiftActions.append(int(action[1:]))
            elif action[0] == 'R':
                rule_num = int(action[1:])
                rule = this.extended_grammar_rules[rule_num]
                rule.RHS = rule.RHS[1:]
                reduceActions.append(rule)

        return Actions(shiftActions, reduceActions)

    def processGrammar(this):
        SUFFIX = "'"

        this.new_start_token = this.input_grammar.StartToken() + SUFFIX
        while this.new_start_token in this.input_grammar.NonTerms():
            new_start_token += SUFFIX

        this.extended_grammar_rules.append(ExtendedRule(this.new_start_token, [DOT, this.input_grammar.StartToken()]))

        for rule in this.input_grammar.Rules():
            tokens = rule.split()
            lhs = ""
            rhs = [DOT]
            for token in tokens:
                if not lhs:
                    lhs = token
                elif token == "->":
                    continue
                elif token == "|":
                    this.extended_grammar_rules.append(ExtendedRule(lhs, rhs))
                    rhs = [DOT]
                else:
                    rhs.append(token)
            this.extended_grammar_rules.append(ExtendedRule(lhs, rhs))

    def findClosure(this,inp_state, token_after_dot):
        #print("\t\tfindClosure",token_after_dot)
        closure = []

        if token_after_dot == this.new_start_token:
            for rule in this.extended_grammar_rules:
                if rule.LHS == token_after_dot:
                    closure.append(copy.deepcopy(rule))
        else:
            closure = copy.deepcopy(inp_state)

        prev_len = -1
        while prev_len != len(closure):
            prev_len = len(closure)

            tmp_closure = []

            for rule in closure:
                if rule.RHS[-1] != DOT:
                    dot_ind = rule.RHS.index(DOT)
                    dot_points_here = rule.RHS[dot_ind + 1]
                    for in_rule in this.extended_grammar_rules:
                        if dot_points_here == in_rule.LHS and not this.is_belong(in_rule, tmp_closure):
                            tmp_closure.append(in_rule)

            for rule in tmp_closure:
                if not this.is_belong(rule, closure):
                    closure.append(copy.deepcopy(rule))

        return closure

    def GOTO(this,state, token):
        #print("\tGOTO",state,token)
        newState = []

        for rule in this.state_dict[state]:
            if rule.RHS[-1] != DOT:
                dotInd = rule.RHS.index(DOT)
                if rule.RHS[dotInd + 1] == token:
                    shiftedRule = copy.deepcopy(rule)
                    shiftedRule.RHS[dotInd] = shiftedRule.RHS[dotInd + 1]
                    shiftedRule.RHS[dotInd + 1] = '.'
                    newState.append(shiftedRule)

        addClosureRules = []
        for rule in newState:
            if rule.RHS[-1] != DOT:
                dotInd = rule.RHS.index(DOT)
                closureRes = this.findClosure(newState, rule.RHS[dotInd + 1])
                for inRule in closureRes:
                    if not this.is_belong(inRule, addClosureRules) and not this.is_belong(inRule, newState):
                        addClosureRules.append(inRule)

        for rule in addClosureRules:
            newState.append(rule)

        stateExists = -1
        for _state in this.state_dict:
            if this.state_dict[_state] == newState:
                stateExists = _state
                break

        if stateExists == -1:
            this.stateCount += 1
            this.state_dict[this.stateCount] = newState
            this.GOTOStateDict[(state, token)] = this.stateCount
        else:
            this.GOTOStateDict[(state, token)] = stateExists

    def computeGOTO(this,state):
        #print("computeGOTO",state)
        for rule in this.state_dict[state]:
            generateStatesFor = set()

            if rule.RHS[-1] != DOT:
                dotInd = rule.RHS.index(DOT)
                dotPointsHere = rule.RHS[dotInd + 1]
                if dotPointsHere not in generateStatesFor:
                    generateStatesFor.add(dotPointsHere)
        
            if generateStatesFor:
                for token in generateStatesFor:
                    this.GOTO(state, token)

    def generateStates(this):
        prevLen = -1
        used = set()

        while len(this.state_dict) != prevLen:
            prevLen = len(this.state_dict)
            keys = this.getKeys(this.state_dict)
            for key in keys:
                if key not in used:
                    used.add(key)
                    this.computeGOTO(key)

    def createParseTable(this):
        v = [''] * (len(this.input_grammar.NonTerms()) + len(this.input_grammar.Terms()) + 1)
        this.table = [copy.deepcopy(v) for _ in range(this.stateCount + 1)]
        #print(this.table)
        non_terms = this.input_grammar.NonTerms()
        terms = this.input_grammar.Terms()

        this.cols = this.findCols()

        for entry in this.GOTOStateDict:
            state = entry[0]
            token = entry[1]
            col = this.cols.index(token)
            #print("GOTOStates:",state,token)
            if token in non_terms:
                this.table[state][col] += str(this.GOTOStateDict[entry])
            if token in terms:
                this.table[state][col] += "S" + str(this.GOTOStateDict[entry]) + " "
        #print("cols",this.cols)
        processed = {}
        c = 0
        #print(this.extended_grammar_rules)
        for rule in this.extended_grammar_rules:
            tmp_rule = copy.deepcopy(rule)
            if DOT in tmp_rule.RHS:
                tmp_rule.RHS.remove(DOT)
            processed[c] = tmp_rule
            c += 1
        #print("processed")
        #for _,rew in processed.items():
            #print("\t",rew.LHS,rew.RHS)
        #print("extended_rules")
        #for rew in this.extended_grammar_rules:
            #print("\t",rew.LHS,rew.RHS)
        #print(this.extended_grammar_rules[0].RHS)
        added_rule = this.extended_grammar_rules[0].LHS + " -> " + this.extended_grammar_rules[0].RHS[1]
        rules = this.input_grammar.Rules()
        rules.insert(0, added_rule)
        for rule in rules:
            tokens = rule.split()
            lhs = ''
            rhs = ''
            multirhs = []

            for token in tokens:
                if not lhs:
                    lhs = token
                elif token == "->":
                    continue
                elif token == "|":
                    rhs = rhs[:-1]
                    multirhs.append(rhs)
                    rhs = ''
                else:
                    rhs += token + " "
        
            rhs = rhs[:-1]
            multirhs.append(rhs)
            if lhs in this.dict:
                this.dict[lhs] += multirhs
            else:
                this.dict[lhs] = multirhs
        #for p,s in this.dict.items():
        #    print("dict:",p,s)
        for state_num, rules in this.state_dict.items():
            for rule in rules:
                if rule.RHS[-1] == DOT:
                    tmp_rule = copy.deepcopy(rule)
                    tmp_rule.RHS.remove(DOT)
                    for key, proc in processed.items():
                        if proc == tmp_rule:
                            used = set()
                            follow_res = this.follow(rule.LHS, used)
                            for col in follow_res:
                                ind = this.cols.index(col)
                                if key == 0:
                                    this.table[state_num][ind] = "acc"
                                else:
                                    this.table[state_num][ind] += "R" + str(key) + " "
    def follow(this,non_term, used):
        sol_set = set()
        if non_term == this.new_start_token:
            sol_set.add(SPEC_TOKEN)
        
        used.add(non_term)

        for cur in this.dict:
            cur_non_term = copy.deepcopy(cur)
            rhs = copy.deepcopy(this.dict[cur])
            for sub_rule in rhs:
                sub_rule_vec=copy.deepcopy(sub_rule.split())
                while non_term in sub_rule_vec:
                    non_term_ind = sub_rule_vec.index(non_term)
                    sub_rule_vec = sub_rule_vec[non_term_ind + 1:]
                    first_res=[]
                    if len(sub_rule_vec) > 0:
                        first_res = this.first(sub_rule_vec, set())
                        if first_res and EPSILON in first_res:
                            ##first_res.remove(EPSILON)
                            start=len(first_res)
                            if EPSILON in first_res:
                                start=first_res.index(EPSILON)
                            first_res=first_res[:start]
                            ans_new = this.follow(cur_non_term, used)
                            first_res.extend(ans_new)
                    else:
                        if non_term != cur_non_term and cur_non_term not in used:
                            first_res = this.follow(cur_non_term, used)
                    if first_res and first_res[0] != NOTHING:
                        sol_set.update(first_res)

        v = set_to_vect(sol_set)
        #print("follow",non_term,v)
        return v
    def first(this,rule, used):
        if rule[0] != NOTHING and rule:
            if rule[0] == EPSILON:
                return [EPSILON]
            if rule[0] in this.input_grammar.Terms():
                return [rule[0]]

            if rule[0] in this.dict:
                res = []
                if rule[0] not in used:
                    used.add(rule[0])
                    rhs = this.dict[rule[0]]
                    for sub_rule in rhs:
                        sub_rule_vect = str_to_vect(sub_rule)
                        in_res = first(sub_rule_vect, used)
                        if in_res and in_res[0] != NOTHING:
                            res.extend(in_res)

                if EPSILON not in res:
                    return res

                res.remove(EPSILON)

                if len(res) > 1:
                    sliced = rule[1:]
                    ans_new = first(sliced, used)
                    if ans_new and ans_new[0] != NOTHING:
                        res.extend(ans_new)
                    return res

                res.append(EPSILON)
                return res
        return [NOTHING]

    
    def getKeys(this,map):
        keys = [key for key in map.keys()]
        return keys
    def findCols(this):
        rows = []
        for term in this.input_grammar.Terms():
            rows.append(term)
        rows.append(SPEC_TOKEN)
        for non_term in this.input_grammar.NonTerms():
            rows.append(non_term)

        return rows

    def __init__(this,grammar:Grammar):
        this.input_grammar=grammar
        this.extended_grammar_rules=[]
        this.state_dict=dict()
        this.GOTOStateDict=dict()
        this.table=[];
        this.cols=[];

        this.dict=dict()

        this.newStartToken=""
        this.stateCount=0
        this.processGrammar()
        #print(*this.extended_grammar_rules)
        #print(this.new_start_token)
        #for t in this.extended_grammar_rules:
         #   print(t.LHS,t.RHS)
        #print()
        tmp=[]
        I0=this.findClosure(tmp,this.new_start_token)
        #for t in I0:
        #    print(t.LHS,t.RHS)
        #print()
        this.state_dict[0]=I0
        this.generateStates()
        #for number, k in this.state_dict.items():
            #print(number)
            #for t in k:
                #print("\t",t.LHS,t.RHS)
        #print()
        this.createParseTable()
        pass
    pass
