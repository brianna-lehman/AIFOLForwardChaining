import sys
import re
import pdb

rules = {}
inferred_rules = []
facts = []
prove = None

def main():
	i = 0
	with open(sys.argv[1], 'r') as kb:
		for line in kb:
			if '->' in line:
				# remove newline from line
				line = line[:-1]

				pattern = re.compile(r"\s*[\^]\s*|\s*->\s*")
				rule_list = pattern.split(line)

				atoms = [rule for rule in rule_list[:-1]]
				inferred_rules.append(rule_list[-1])
				rules[i] = atoms
				print("%d: %s" %(i,rules[i]))
				i += 1

			elif 'PROVE' in line:
				# remove 'PROVE   ' from line
				global prove

				pattern = re.compile(r"PROVE\s*")
				prove = pattern.sub("", line)

			else:
				line = line[:-1]
				facts.append(line)
				print("%s added to list of facts" %line)

	print("Inferred rules: %s" %inferred_rules)

	checkFacts()

	print("%s is not provable" %prove)

def checkFacts():
	# while there are inferred rules that haven't been added to the knowledge base
	while not contains(inferred_rules,facts):
		print("Facts:%s before trying to prove statement" %facts)
		print("Not all inferred rules are facts, yet")
		# go through all the statements
		for index, rules_list in rules.items():
			inferred_rule = inferred_rules[index]
			temp_rules = rules_list[:]
			temp_facts = facts[:]
			print("\tLooking at %s: %s" %(inferred_rule, rules_list))

			# compare all the rules in this statement to every fact that hasn't been substituted already
			for rule in rules:
				for fact in temp_facts:
					print("\t\tTry to unify %s with %s" %(rule,fact))
					# try to unify each rule with each fact
					substitutions = unify(rule,fact)
					# if substitution is possible
					if substitutions:
						print("\t\t%s for %s/%s" %(substitutions,rule,fact))

						# replace all the variables on the left and right side of the statement
						# with their substitution constants
						for var,const in substitutions.items():
							for i,r in enumerate(temp_rules):
								if var in getValues(r):
									# [4 if x==1 else x for x in a]
									print("\t\t\tReplacing %s in %s with %s" %(var,r,const))
									temp_rules[i] = replace(r,var,const)
									print("\t\t\t%s" %temp_rules[i])

									# remove the atom from the left side - it's true
									if not hasVariable(temp_rules[i]):
										print("\t\t\t%s has no variables. Remove it from current list of rules" %temp_rules[i])
										print("\t\t\tOld list: %s" %temp_rules)
										temp_rules.remove(temp_rules[i])
										print("\t\t\tNew list: %s" %temp_rules)

							if var in getValues(inferred_rule):
								inferred_rules[index] = replace(inferred_rule,var,const)

						# remove the fact from temp_facts since it's already been substituted w/ a rule
						temp_facts.remove(fact)
						print("\t\t%s removed from %s. No other rules will will be compared with %s" %(fact,temp_facts,fact))

						# stop trying to find a fact for this rule, we've already found one
						break

				print("\t\tTemp Rules: %s" %temp_rules)

			# if all the rules on the left side of the statment have been substituted and are true
			if not temp_rules:
				# check if the inferred rule for this statement is the fact we're trying to prove
				if inferred_rules[index] == prove:
					print("%s is proved" %inferred_rules[index])
					exit()
				# add the inferred rule to the list of facts if it's not already there
				elif inferred_rules[index] not in facts:
					print("\tTemp:%s is empty so %s is added is added to list of facts" %(temp_rules,inferred_rules[index]))
					facts.append(inferred_rules[index])
					print("\tFacts:%s" %facts)

def unify(rule, fact):
	# if the variables in rule can be matched w/ the constants in fact
	# return the dictionary of variable:constant substitutions
	substitutions = {}
	removeRuleConstants = []
	rule_vals = getValues(rule)
	fact_vals = getValues(fact)

	if getPredicate(rule) != getPredicate(fact) or len(rule_vals) != len(fact_vals):
		return None
	if len(rule_vals) == len(fact_vals):
		substitutions = dict(zip(rule_vals, fact_vals))

	for a1, a2 in substitutions.items():
		if not isVariable(a1) and not isVariable(a2) and (a1 != a2):
			return None
		if not isVariable(a1):
			removeRuleConstants.append(a1)

	for rule_constant in removeRuleConstants:
		substitutions.pop(rule_constant)

	return substitutions

def replace(rule, variable, constant):
	pattern = r"(?<=\(|,)("+variable+")"
	return re.sub(pattern, constant, rule)

def isVariable(val):
	if len(val) == 1 and val.islower():
		return True
	else:
		return False

def isConstant(val):
	return not isVariable(val)

def contains(list_of_rules, list_of_facts):
	set(list_of_rules).issubset(list_of_facts)

def hasVariable(atom):
	# returns true if any value inside predicate() is a variable
	values = getValues(atom)
	if values is None:
		return False

	for v in values:
		if len(v) == 1 and v.islower():
			return True

	return False

def isConstant(atom):
	# returns true if all values inside predicate() are constant
	return not hasVariable(atom)

def getValues(atom):
	# returns the value inside predicate()
	value_match = re.search("\((.*?)\)", atom)
	if value_match:
		value_str = value_match.group(0)
		value_str = value_str[1:-1]
		return value_str.split(",")
	else:
		return None

def getPredicate(atom):
	# returns predicate w/out value
	predicate_match = re.search("(.*?)(?=\()", atom)
	if predicate_match:
		return predicate_match.group(0)
	else:
		return None

if __name__ == "__main__":
	main()