import sys
import re
import pdb

statements = {}
inferred_rules = []
kb = []
prove = None
inferred_arguments = []

def main():
	i = 0
	filename = sys.argv[1]
	with open(filename, 'r') as file:
		for line in file:
			if '->' in line:
				# remove newline from line
				line = line[:-1]

				pattern = re.compile(r"\s*[\^]\s*|\s*->\s*")
				rule_list = pattern.split(line)

				atoms = [rule.replace(" ", "") for rule in rule_list[:-1]]
				inferred_rules.append(rule_list[-1])
				statements[i] = atoms
				print("%d: %s -> %s" %(i,statements[i],inferred_rules[i]))
				i += 1

			elif 'PROVE' in line:
				# remove 'PROVE   ' from line
				global prove

				pattern = re.compile(r"PROVE\s*")
				prove = pattern.sub("", line).replace(" ", "")

			else:
				line = line[:-1]
				kb.append(line.replace(" ", ""))

	print("List of kb: %s" %kb)
	print("Prove: %s" %prove)

	proved = check()

	if proved == True:
		print("%s is true" %prove)
	else:
		print("%s is unprovable" %prove)

	createTranscript(filename,proved)

def check():
	new = ["temp"]

	while new:
		new = []
		for index, statement in statements.items():
			temp_kb = kb[:]
			conclusion = inferred_rules[index]
			print("Looking at statement %s -> %s" %(statement,conclusion))
			for atom in statement:
				if hasVariable(atom):
					print("Atom to look at this iteration: %s" %atom)
					print("Facts to look at this iteration: %s" %temp_kb)
					fact = getFact(atom,temp_kb)
					print("%s unifiable with %s" %(atom,fact))
					if fact is not None:
						substitutions = unify(atom,fact)
						for var,const in substitutions.items():
							for i,a in enumerate(statement):
								print("Replace %s in %s with %s" %(var,a,const))
								statement[i] = replace(a,var,const)
							if var in getValues(conclusion):
								inferred_rules[index] = replace(conclusion,var,const)
								conclusion = inferred_rules[index]
						temp_kb.remove(fact)
						print("Modified list of facts to look at next iteration: %s" %temp_kb)

				print("Statement: %s -> %s" %(statement,conclusion))

			if not statementHasVariable(statement) \
			and not hasVariable(conclusion) \
			and conclusion not in kb \
			and conclusion not in new:
				print("Add %s to kb" %conclusion)
				new.append(conclusion)
				inferred_arguments.append(conclusion)

				if conclusion == prove:
					return True
		kb.extend(new)

	return False

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

def createTranscript(filename,proved):
	filename = format(filename)
	transcript = open(str(filename)+"_out_IFC.txt", "w")
	transcript.write("Inferred Arguments: %s" %inferred_arguments)
	if proved:
		transcript.write("\n%s is proved" %prove)
	else:
		transcript.write("\n%s is unprovable" %prove)
	transcript.close()

def format(string):

	if "\\" in string:
		val = string.split("\\")[1]
	if "/" in string:
		val = string.split("/")[1]

	return val


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
		return value_index, statements[value_index]
	else:
		return value_index, None

def predicateInFacts(rule):
	for fact in kb:
		if getPredicate(rule) == getPredicate(fact):
			return True
	return False

def getFact(rule,facts=kb):
	for f in facts:
		if getPredicate(rule) == getPredicate(f):
			values_dict = dict(zip(getValues(rule), getValues(f)))
			for r_val, f_val in values_dict.items():
				if not isVariable(r_val) and r_val != f_val:
					return None
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
		value_str = value_str.replace(" ", "")
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