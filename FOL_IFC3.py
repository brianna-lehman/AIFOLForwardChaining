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

	print("Inferred rules: %s\n" %inferred_rules)

	check(prove)

	print("\n%s is not provable" %prove)

def check(fact):
	# find the inferred rule with same predicate as prove fact
	inferred_rule = getInferredRule(fact)
	if inferred_rule is None:
		print("There are no inferred rules for this conclusion (%s)." %fact)
		return

	# get the list of rules that will result in this inferred rule being true
	inferred_rule_index, rule_list = getRulesDictionary(inferred_rule)
	if rule_list is None:
		print("This is no list of rules associated with this inferred rule (%s)." %inferred_rule)
		return

	print("Given the atom to be proved (%s): \n\t1.) find the inferred_rule (%s)\n\t2.) find the list of rules to make it true (%s)" %(fact,inferred_rule,rule_list))

	for rule in rule_list:
		f = getFact(rule)
		if f is None:
			print("This rule (%s) can't currently be proved. It doesn't have a corresponding fact in the KB" %rule)
			check(rule)
			f = getFact(rule)
			print("This rule (%s) should now be in the KB" %rule)

		if f:
			print("This rule (%s) is in the KB." %rule)
			substitutions = unify(rule,f)
			if substitutions is not None:
				for var,const in substitutions.items():
					for i,r in enumerate(rule_list):
						rule_list[i] = replace(r,var,const)
					if var in inferred_rule:
						inferred_rules[inferred_rule_index] = replace(inferred_rule,var,const)
						inferred_rule = inferred_rules[inferred_rule_index]

			print("After the replacement of variables: %s:%s" %(inferred_rule,rule_list))

			if not statementHasVariable(rule_list):
				if inferred_rules[inferred_rule_index] == prove:
					print("%s is proved" %prove)
					exit()
				else:
					print("There are no variables in the statment %s" %rule_list)
					print("%s is now a fact and will be added to the database" %inferred_rules[inferred_rule_index])
					facts.append(inferred_rules[inferred_rule_index])
					return

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

def getInferredRule(fact):
	for rule in inferred_rules:
		if getPredicate(rule) == getPredicate(fact):
			return rule
	return None

def getRulesDictionary(conclusion):
	try:
		value_index = inferred_rules.index(conclusion)
	except:
		value_index = -1

	if value_index != -1:
		return value_index, rules[value_index]
	else:
		return value_index, None

def predicateInFacts(rule):
	for fact in facts:
		if getPredicate(rule) == getPredicate(fact):
			return True
	return False

def getFact(rule):
	for f in facts:
		if getPredicate(rule) == getPredicate(f):
			return f
	return None

def statementHasVariable(list):
	for atom in list:
		if hasVariable(atom):
			return True
	return False

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