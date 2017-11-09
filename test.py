import re

def main():
	rules = ["American(x)", "Weapon(y)", "Nation(z)", "Hostile(z)", "Sells(x,z,y)", "Criminal(x)"]
	dictionary_of_rules = {x:False for x in rules[:-1]}
	print(dictionary_of_rules)

def unify(rule, fact):
	# if the variables in rule can be matched w/ the constants in fact
	# return the dictionary of variable:constant substitutions
	substitutions = {}
	removeRuleConstants = []
	rule_vals = getValues(rule)
	print("\tRule values - %s: %s" %(rule,rule_vals))
	fact_vals = getValues(fact)
	print("\tFact values - %s: %s" %(fact,fact_vals))

	if getPredicate(rule) != getPredicate(fact) or len(rule_vals) != len(fact_vals):
		print("\t%s != %s or %d != %d" %(getPredicate(rule), getPredicate(fact), len(rule_vals), len(fact_vals)))
		return None
	if len(rule_vals) == len(fact_vals):
		print("\t%s == %s" %(len(rule_vals), len(fact_vals)))
		substitutions = dict(zip(rule_vals, fact_vals))
		print("\t%s" %substitutions)

	for a1, a2 in substitutions.items():
		print("\t%s:%s" %(a1,a2))
		if not isVariable(a1) and not isVariable(a2) and (a1 != a2):
			print("\t%s and %s and (%s != %s)" %(isConstant(a1),isConstant(a2),a1,a2))
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
	print("\t\t%s" %val)
	if len(val) == 1 and val.islower():
		print("\t\t%s == 1 and %s" %(len(val),val.islower()))
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