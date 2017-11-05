import sys
import re

rules = []
facts = []
prove = None

def main():
	with open(sys.argv[1], 'r') as kb:
		for line in kb:
			if '->' in line:
				# remove newline from line
				line = line[:-1]

				pattern = re.compile(r"  \^  |  ->  ")
				rule_list = pattern.split(line)

				rule_dict = {rule:False for rule in rule_list}
				rules.append(rule_dict)

			elif 'PROVE' in line:
				# remove 'PROVE   ' from line
				prove = line[8:]

			else:
				addFact(line)
				print()

def addFact(fact):
	print("Adding %s to list of facts" %fact)
	if fact == prove:
		print("%s proved" %prove)
		exit()

	for rule_dict in rules:
		# try to unify every rule in the rule dictionary with the given fact
		for rule, isProved in rule_dict.items():
			print("\t%s: %s" %(rule,isProved))
			substitutions = unify(rule, fact)
			# if the current rule can be unified with the fact
			if substitutions is not None:
				# replace all the variables in the current dictionary
				# with their corresponding constant
				for rule, isProved in rule_dict.items():
					for var, constant in substitutions.items():
						if var in getValues(rule):
							newRule = replace(rule, var, constant)
							rule_dict[newRule] = rule_dict.pop(rule)

							# move the second to last dictionary element to the end of the dictionary
							end_rule = rule_dict.keys()[-2]
							end_rule_value = rule_dict.pop(end_rule)
							rule_dict[end_rule] = end_rule_value

					if not hasVariable(rule):
						rule_dict[rule] = True
				# stop trying to find a new unification in this dictionary
				break
			print("\t%s: %s" %(rule,isProved))

		# if all the rules have been proved and the implied rule has no remaining variables
		# remove this dictionary of rules from the list of all rules
		# add the implied rule to the list of facts
		if False not in rule_dict.values():
			newFact = rule_dict.keys()[-1]
			if !hasVariable(newFact):
				rules.remove(rule_dict)
				addFact(newFact)



def unify(rule, fact):
	# if the variables in rule can be matched w/ the constants in fact
	# return the dictionary of variable:constant substitutions
	substitutions = {}
	rule_vals = getValues(rule)
	fact_vals = getValues(fact)
	if getPredicate(rule) != getPredicate(fact) or len(rule_vals) != len(fact_vals):
		return None
	if len(rule_vals) == len(fact_vals):
		substitutions = dict(zip(rule_vals, fact_vals))

	for a1, a2 in substitutions.items():
		if isConstant(a1) and isConstant(a2) and a1 != a2:
			return None
		if isConstant(a1)
			substitutions.pop(a1)

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

def hasVariable(atom):
	# returns true if any value inside predicate() is a variable
	values = getValues(atom)
	if values is None:
		print("This atom has no values")
		return False

	for v in values:
		if len(v) == 1 and v.islower():
			return True

	return False

def isConstant(atom):
	# returns true if all values inside predicate() are constant
	return !hasVariable(atom)

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