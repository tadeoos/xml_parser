# -*- coding: utf-8 -*-

from Kubas_module.cons import *
from termcolor import colored
import codecs
import lxml.etree as etree
import os
from termcolor import colored


def multiplatform_path(string):
    return(os.path.join(os.path.splitdrive(string)[0], os.sep, *re.split("[\\/\\\]", string)[1:]))

def inner_path(string):
    return(os.path.join(*re.split("[\\/\\\]", string)))


# test dictionary
test_dict = {
	'lemma(X7) \in {SO, TOO, ALSO}' : '<Atom><!--lemma(X7) \in {SO, TOO, ALSO}--><Rel>isIn</Rel><Set><Ind>SO</Ind><Ind>TOO</Ind><Ind>ALSO</Ind></Set><Expr><Fun>lemma</Fun><Var>X7</Var></Expr></Atom>',
	'coreferential(X1,X5)' : '<Atom><!--coreferential(X1,X5)--><Rel>coreferential</Rel><Var>X1</Var><Var>X5</Var></Atom>',
	'gradable_antonyms(X3,X5)' : '<Atom><!--gradable_antonyms(X3,X5)--><Rel>gradable_antonyms</Rel><Var>X3</Var><Var>X5</Var></Atom>',
	'lemma(X2) = lemma(X4)' : '<Equal><!--lemma(X2) = lemma(X4)--><Expr><Fun>lemma</Fun><Var>X2</Var></Expr><Expr><Fun>lemma</Fun><Var>X4</Var></Expr></Equal>',
	'adlative(X2) or ablative(X2) or perlative(X2)' : '<Or><!--adlative(X2) or ablative(X2) or perlative(X2)--><Atom><!--adlative(X2)--><Rel>adlative</Rel><Var>X2</Var></Atom><Atom><!--ablative(X2)--><Rel>ablative</Rel><Var>X2</Var></Atom><Atom><!--perlative(X2)--><Rel>perlative</Rel><Var>X2</Var></Atom></Or>',
	'UE({X1})' : '<Atom><!--UE({X1})--><Rel>UE</Rel><Set><Var>X1</Var></Set></Atom>',
	'\exists Z1 adv_adj_pair(X3,Z1)' : '<Exists><!--\exists Z1 adv_adj_pair(X3,Z1)--><Atom><!--adv_adj_pair(X3,Z1)--><Rel>adv_adj_pair</Rel><Var>X3</Var><Var>Z1</Var></Atom><Var>Z1</Var></Exists>',
	'lemma(X5) = DO' : '<Equal><!--lemma(X5) = DO--><Expr><Fun>lemma</Fun><Var>X5</Var></Expr><Ind>DO</Ind></Equal>',
	'~(relational(X3))' : '<Neg><Atom><!--~(relational(X3))--><Rel>relational</Rel><Var>X3</Var></Atom></Neg>',
	'int(X2) > int(Y1)' : '<GreaterThan><!--int(X2) > int(Y1)--><Expr><Fun>int</Fun><Var>X2</Var></Expr><Expr><Fun>int</Fun><Var>Y1</Var></Expr></GreaterThan>',
	'int(Y2) = int(X4) + 1' : '<unknown>int(Y2) = int(X4) + 1</unknown>',
	'asd[ac] 3rr' : '<unknown>asd[ac] 3rr</unknown>',
}

# scrut_dict = {
# 	 intersective(X2) : 1

# }



# Make a list of rules
with codecs.open(inner_path("..\..\REGUŁY\REGUŁY_SFORMALIZOWANE_ver_0923.txt"), 'r', encoding='utf-8') as infile:
	corpus_feed = infile.read()

raw_split = re.split('(^Rx?\d+?.*?:)', corpus_feed, flags=re.MULTILINE)
good_split = [a+b for a,b in zip(raw_split[1::2], raw_split[2::2])]
rules = [rl(raw_rule) for raw_rule in good_split]

# cos = etree.fromstring('<Equal><Expr><Fun>tense</Fun><Var>X1</Var></Expr><Expr><Fun>tense</Fun><Var>Y1</Var></Expr></Equal>')

def test(rob=False):
	print('\n--TESTY\n')
	errors = []
	passed = []
	corners = []
	for key in test_dict.keys():
		test_node = Constraints_Node(test=[key])
		left = test_node.cons_to_element()
		right = etree.fromstring('<Constraints>'+''.join(test_dict[key])+'</Constraints>')
		pr_left = etree.tostring(left, encoding='unicode')
		pr_right = etree.tostring(right, encoding='unicode')
		try:
			assert pr_left == pr_right
			if 'unknown' in pr_left:
				corners.append(key)
			else:
				passed.append(key)
		except Exception as e:
			# print('ERROR!\nL: {}\nR: {}'.format(pr_left, pr_right))
			errors.append(key)
	
	for key in passed:
		print('PASSED TEST: ', end='')
		print(colored(key, 'green'))
	print()
	for key in errors:
		print('FAILED TEST: ', end='')
		print(colored(key, 'red'))
	print()
	for key in corners:
		print('UNKNOWN CASE: ', end='')
		print(colored(key, 'blue'))

	if rob:
		print('\n--SCRUTS\n')	
		for key in errors:
			print('CSTR: ',key)
			print(test_node.scrutinize(key))
			print('\nMAKE NODE\n')
			root = etree.Element("Constraints")
			make = test_node.make_node(root, key)
			try:
				print(etree.tostring(make, pretty_print=True, encoding='unicode'))
			except Exception as e:
				print('COŚ NIE WESZŁo')
				print(make)

def print_all():
	for rule in rules:
		cons_node = Constraints_Node(rule)
		# if cons_node.parse() is not None:
		# wykomentowuję poniżej do testów JK
		print(cons_node.rule_name)
		# print(cons_node.consts)
		print(cons_node)

def show_errors():
	for rule in rules:
		cons_node = Constraints_Node(rule)
		cons_node.parse()
		print(cons_node.errors) if len(cons_node.errors) != 0 else None


test()

