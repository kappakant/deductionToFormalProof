# Given an axiomatic proof utilizing an assumption by deduction theorem or an element in Gamma, return a valid axiomatic proof
# that does not use deduction theorem or gamma

# i.e.
# given either a proof of the form Gamma U S |- P or Gamma |- P with S used in deduction, returns a 
# formal axiomatic proof of the form |-  S > P

# - = \neg
# > = \rightarrow
# Premise = phi s.t. phi in Gamma
# Deduction 
# 1 = PL1 or A -> (B -> A)
# 2 = PL2 or (A -> (B -> C)) -> ((A -> B) -> (A -> C))
# 3 = PL3 or (~B -> ~A) -> ((~B -> A) -> B)
# lines demarcated by \n

textFile = "pfromnotnotp.txt"
with open(textFile) as tf:
    axiomaticProof = tf.readlines()
    axiomaticProof = [x.strip() for x in axiomaticProof]

# determines whether to encase phi in parentheses or not
def embedd(phi):
    if ">" in phi:
        return f"({phi.strip()})"
    else:
        return phi.strip()
    
def disembedd(phi):
    phi = phi.strip()
    if len(phi) > 1 and phi[1] == "(" and phi[len(phi)-2] == ")":
        return phi[1:len(phi)-1]
    else:
        return phi

def deductionToFormal(proof, antecedent):
    firstStep = []
    for line in proof:
        schema, rule = line.split("|")
        firstStep.append(f"{embedd(antecedent)} > {embedd(schema)}|{rule}")

    lenToSkip = len(embedd(antecedent)) + 2

    newProof = []

    # returns (m, n) where m is the antecedent and mp is the whole
    def findMP(mp):
        mpantecedent = ""
        if mp[0] != "(":
            for i in mp:
                if i == ">":
                    break
                else:
                    mpantecedent += 1

        # accumulate letters until parentheses are balanced.
        else:
            l = 0
            r = 0
            for i in mp:
                if i == "(":
                    l += 1
                if i == ")":
                    r += 1
                
                mpantecedent += i
                if l == r:
                    break

        mpantecedentindex = -1
        for index, i in enumerate(newProof[:newProof.index(mp)]):
            if (i[:len(mpantecedent)-2] == mpantecedent[1:len(mpantecedent)-1]):
                mpantecedentindex = index
                break
        
        return (mpantecedentindex + 1, newProof.index(mp) + 1)

    for line in firstStep:
        schema, rule = line.split("|")
        originalLine = disembedd(schema[lenToSkip:])
        rule = rule.strip("() ")

        if rule == "1" or rule == "2" or rule == "3":
                newProof.append(f"{originalLine}|{rule}")
                newProof.append(f"{embedd(originalLine)} > ({embedd(antecedent)} > {embedd(originalLine)})|{1}")
                newProof.append(f"{embedd(antecedent)} > {embedd(originalLine)}|{(len(newProof)-1, len(newProof))}")


        if rule == "Premise" and antecedent == originalLine:
            newProof.append(f"({embedd(antecedent)} > (({embedd(antecedent)} > {embedd(antecedent)}) > {embedd(antecedent)})) > (({embedd(antecedent)} > ({embedd(antecedent)} > {embedd(antecedent)})) > ({embedd(antecedent)} > {embedd(antecedent)}))|{2}")
            newProof.append(f"{embedd(antecedent)} > (({embedd(antecedent)} > {embedd(antecedent)}) > {embedd(antecedent)})|{1}")
            newProof.append(f"{embedd(antecedent)} > {embedd(antecedent)}|{(len(newProof)-1, len(newProof))}")


        elif rule == "Premise" or rule == "Deduction":
            newProof.append(f"{originalLine}|{rule}")
            newProof.append(f"{embedd(originalLine)} > ({antecedent} > {embedd(originalLine)})|{1}")
            newProof.append(f"{embedd(antecedent)} > {embedd(originalLine)}|{(len(newProof)-1, len(newProof))}")

        if "," in rule: #MP case
            leftIndex, rightIndex = rule.split(", ")
            zk = originalLine

            leftLine = proof[int(leftIndex)-1]
            rightLine = proof[int(rightIndex)-1]

            leftSchema, leftRule = leftLine.split("|")
            rightSchema, rightRule = rightLine.split("|")

            zi = min(leftSchema, rightSchema, key=len)
            zj = max(leftSchema, rightSchema, key=len)

            zi = zi.strip()
            zk = zk.strip()
            
            mpPL2instance = f"({embedd(antecedent)} > ({embedd(zi)} > {embedd(zk)})) > (({embedd(antecedent)} > {embedd(zi)}) > ({embedd(antecedent)} > {embedd(zk)}))|{2}"
            newProof.append(mpPL2instance)
            mp1, mp2 = findMP(mpPL2instance)

            mpmpinstance = f"({embedd(antecedent)} > {embedd(zi)}) > ({embedd(antecedent)} > {embedd(zk)})|({mp1}, {mp2})"
            newProof.append(mpmpinstance) 

            mp3, mp4 = findMP(mpmpinstance)
            newProof.append(f"{embedd(antecedent)} > {embedd(zk)}|({mp3}, {mp4})")

    cleanerNewProof = [f"{f"{index}.":<3} {line}" for index, line in zip(range(1, len(newProof)+1), newProof)]
    return cleanerNewProof

## MODUS PONENS DOES NOT MAP TO CORRECT INDICES

test = deductionToFormal(axiomaticProof, "--P")

for line in test:
    print(line)
'''
for line in axiomaticProof:
    schema, rule = line.split("|")
''' 
