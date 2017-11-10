import sys
import re
import pdb

rules = {}
implied_rules = []
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
				implied_rules.append(rule_list[-1])
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

	print("Implied rules: %s" %implied_rules)

	for fact in facts:
		checkFact(fact)
	print("%s is not provable" %prove)

def checkFact(fact):
	if fact == prove:
		print("%s is proved" %fact)
		exit()

	if fact not in facts:
		print("Infered fact %s added to list of facts" %fact)
		facts.append(fact)

	print("Checking %s against rules" %fact)

	for index, rule_list in rules.items():
		all_rules_proved = True
		for rule in rule_list:
			substitutions = unify(rule,fact)
			if substitutions is not None:
				# for every substitution
				for var, const in substitutions.items():
					# check every rule in the list to see if var can be replaced
					for i, r in enumerate(rule_list):
						if var in getValues(r):
							rule_list[i] = replace(r,var,const)

					# check the implied rule associated with this list for variables
					# that can be substituted
					implied_rule = implied_rules[index]
					if var in getValues(implied_rule):
						implied_rules[index] = replace(implied_rule,var,const)

			if hasVariable(rule):
				all_rules_proved = False

		if all_rules_proved \
		   and not hasVariable(implied_rules[index]) \
		   and implied_rules[index] not in facts:
			checkFact(implied_rules[index])


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