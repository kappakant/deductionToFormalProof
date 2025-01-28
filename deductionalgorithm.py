# Given an axiomatic proof utilizing an assumption by deduction theorem, return a valid axiomatic proof
# that does not use deduction theorem

# MODUS PONENS POINT TO WRONG INDICES
# USING PREMISES FROM GAMMA OTHER THAN ANTECEDENT IS NOT SUPPORTED
# This is not a very good implementation, but I haven't found any other scripts for this. 

# - = \neg
# > = \rightarrow
# lines demarcated by \n

with open("pfromnotnotp.txt") as example:
    axiomaticProof = example.readlines()
    axiomaticProof = [x.strip() for x in axiomaticProof]

def deductionToFormal(proof, antecedent):
    firstStep = []
    for line in proof:
        firstStep.append(f"{antecedent} > {line}")

    lenToSkip = len(antecedent) + 2

    newProof = []
    newProofIndex = 1

    oldIndex = 1
    oldToTrue = {}
    for line in firstStep:
        schema, rule = line.split("|")
        originalLine = schema[lenToSkip:].strip()

        if rule == "1" or rule == "2" or rule == "3":
                newProof.append(f"{newProofIndex}.{originalLine}|{rule}")
                newProofIndex += 1

                newProof.append(f"{newProofIndex}.({originalLine}) > ({antecedent} > ({originalLine}))|{1}")
                newProofIndex += 1

                newProof.append(f"{newProofIndex}.({antecedent} > ({originalLine}))|{(len(newProof)-1, len(newProof))}")
                newProofIndex += 1

                oldToTrue[oldIndex] = newProofIndex-1

        if rule == "Premise": # no support for using other premises in Gamma
            newProof.append(f"{newProofIndex}. ({antecedent} > (({antecedent} > {antecedent}) > {antecedent})) > (({antecedent} > ({antecedent} > {antecedent})) > ({antecedent} > {antecedent}))|{2}")
            newProofIndex += 1

            newProof.append(f"{newProofIndex}. ({antecedent} > (({antecedent} > {antecedent}) > {antecedent}))|{1}")
            newProofIndex += 1

            newProof.append(f"{newProofIndex}. ({antecedent} > {antecedent})|{(len(newProof)-1, len(newProof))}")
            newProofIndex += 1

            oldToTrue[oldIndex] = newProofIndex-1

        if "(" in rule: #MP case
            leftIndex, rightIndex = rule.strip("()").split(", ")
            zk = originalLine

            leftLine = proof[int(leftIndex)-1]
            rightLine = proof[int(rightIndex)-1]

            leftSchema, leftRule = leftLine.split("|")
            rightSchema, rightRule = rightLine.split("|")

            zi = min(leftSchema, rightSchema, key=len)
            zj = max(leftSchema, rightSchema, key=len)

            zi = zi.strip()
            zk = zk.strip()
            
            '''print(leftSchema)
            print(rightSchema)
            print("\n")'''

            '''provedAxioms = [x.split("|")[0].strip("1234567890. ") for x in newProof]
            print(provedAxioms)'''
            print(oldToTrue)

            newProof.append(f"{newProofIndex}. ({antecedent} > (({zi}) > ({zk}))) > (({antecedent} > ({zi})) > ({antecedent} > {zk}))|{2}")
            newProofIndex += 1

            newProof.append(f"{newProofIndex}. ({antecedent} > ({zi})) > ({antecedent} > ({zk}))|({oldToTrue[int(leftIndex)]}, {oldToTrue[int(rightIndex)]})") # modus ponens
            newProofIndex += 1

            newProof.append(f"{newProofIndex}. {antecedent} > ({zk})|({oldToTrue[int(leftIndex)]}, {oldToTrue[int(rightIndex)]+1})")
            newProofIndex += 1

            '''print(newProof[newProofIndex-5])
            print(newProof[newProofIndex-4])
            print(newProof[newProofIndex-3])
            print(newProof[newProofIndex-2])
            print("\n")'''

            oldToTrue[oldIndex] = newProofIndex-1
        oldIndex += 1
    return newProof

## MODUS PONENS DOES NOT MAP TO CORRECT INDICES

test = deductionToFormal(axiomaticProof, "--P")

for line in test:
    print(line)
'''
for line in axiomaticProof:
    schema, rule = line.split("|")
''' 
