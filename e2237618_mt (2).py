class Clause:
    def __init__(self, name, const, negate, child=None):
        self.name = name
        self.const = const
        self.negate = negate
        self.child = child
def cnfparser(clauselist):
    cnf = []
    for x in clauselist:
        splitted = x.split("+")
        clauses = []
        for y in splitted:
            clause = recparser(y)

            clauses.append(clause)
        cnf.append(clauses)
    return cnf
def recparser(clause_string):
    result_list=[]
    index = clause_string.find("(")
    name = clause_string[1:index] if clause_string[0].startswith("~") else clause_string[0:index]
    negate = True if clause_string.startswith("~") else False
    rest=clause_string[index+1:-1]
    const = [c.strip() for c in rest.split(",")]
    num_of_para_open =0
    num_of_para_close = 0
    result=''
    for i in range(0,len(const)):
        for j in range(0,len(const[i])):
            if const[i][j]=='(':
                num_of_para_open+=1
            elif const[i][j] == ')':
                num_of_para_close+=1

        if num_of_para_open > num_of_para_close:
            result+=const[i]+','

        elif num_of_para_open == num_of_para_close:
            result += const[i]
            result_list.append(result)
            result=''
            num_of_para_close=0
            num_of_para_open=0
    res_clause = Clause(name, result_list, negate)
    return res_clause


def clausecreateor(clauses):
    result = ""
    for indx, clause in enumerate(clauses):
        lenght_of_para = 0
        while clause:
            lenght_of_para += 1
            if clause.negate:
                result += "~"
            result += clause.name
            result += "("
            for jindex, j in enumerate(clause.const):
                result += j
                if jindex + 1 != len(clause.const):
                    result += ","
            clause = clause.child
            if clause:
                result += ","
        for j in range(0,lenght_of_para):
            result += ")"
        if len(clauses) > 1 and indx != len(clauses) - 1:
            result += "+"
    return result


def clause_reduce(changable_list, changeable, replacement_list, replacement):
    replacement_list.remove(replacement)
    changable_list.remove(changeable)
    
    first_list = replacement_list
    second_list = changable_list
    for ind in first_list:
        for indx1, const_item  in enumerate(ind.const):
            for indx2, k in enumerate(replacement.const):
                if (const_item  == k):
                    ind.const[indx1] = changeable.const[indx2]
        childi = ind.child
        while childi:
            for indx1, const_item  in enumerate(childi.const):
                for indx2, k in enumerate(replacement.const):
                    if (const_item  == k):
                        childi.const[indx1] = changeable.const[indx2]
            childi = childi.child
    for ind in second_list:
        for indx1, const_item  in enumerate(ind.const):
            for indx2, k in enumerate(changeable.const):
                if (const_item  == k):
                    ind.const[indx1] = replacement.const[indx2]
        childi = ind.child
        while childi:
            for indx1, const_item  in enumerate(childi.const):
                for indx2, k in enumerate(changeable.const):
                    if (const_item  == k):
                        childi.const[indx1] = replacement.const[indx2]
            childi = childi.child
    return first_list + second_list
def theorem_helper(cnf1, cnf2, result):
    cnf1_orj=cnf1
    cnf2_orj=cnf2
    for cnf2index, list2 in enumerate(cnf2_orj):
        for i in list2:
            for cnf1index, list1 in enumerate(cnf1_orj):
                for k in list1:
                    if (i.name == k.name and i.negate != k.negate):
                        tmp = clausecreateor(
                            list2) + "$" + clausecreateor(list1) + "$"
                        reduced = clause_reduce(list2, i, list1, k)
                        list2.append(i)
                        list1.append(k)
                        cnf1.pop(cnf1index)
                        if reduced == []:
                            result.append(tmp + "empty")
                            return [], [], result
                        else:
                            result.append(tmp + clausecreateor(reduced))
                            cnf1.insert(cnf1index, reduced)
                            cnf2.append(reduced)
                            return theorem_helper(cnf1, cnf2, result)
    return cnf1, [], result
def theorem_prover(list1, list2):
    # try:
    result = []
    cnf1 = cnfparser(list1)
    cnf2 = cnfparser(list2)
    while cnf2:
        cnf1, cnf2, result = theorem_helper(cnf1, cnf2, result)
        if cnf1 == []:

            return ("yes", result)
    return ("no", [])