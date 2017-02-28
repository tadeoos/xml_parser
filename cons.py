import lxml.etree as etree
import re


#helper functions

def check_simple(s):
	if (s in ";:,'" and len(s)==1) or s=="'S":
		return True
	if '_' in s:
		return s.replace('_', "").isalnum()
	return s.isalnum()

def preprocess(s):
	# insert space before and after the operator
	for c in '<>+-=':
		c = '\+' if c == '+' else c
		pat1 = r'(.+\S)({})(\S.+)'.format(c)
		pat2 = r'\1 \2 \3'
		s = re.sub(pat1, pat2, s)
	# convert '<' operator to '>' operator
	if ' < ' in s:
		res =  ' > '.join(reversed(s.split(' < ')))
		assert '<' not in res
		return res
	else:
		return s

#This Class takes a rule and parses it in order to obtain an XML <contraints> node
class Constraints_Node(object):

	patterns = {
	"rel": "(?P<rel>^\w+)\((?P<vars>.+)\)$",
	'in': "(?P<expr>^.+)\s.?in (?P<set>{.+})$",
	'fun': "(?P<left>.+?) *[>\+] *(?P<right>.+)",
	'eq': "(?P<left>.+?) *= *(?P<right>.+)",
	'exs': ".+exists (?P<avar>.+) (?P<expr>.+)",
	'or': "(?P<vars>.+) or .+",
	'neg' : "~\((?P<neg>.+)\)",
	'opr' : ".+[\+=\*].+",
	}
	pat = {key:re.compile(value, flags=re.MULTILINE) for (key,value) in patterns.items()}

	def __init__(self, rule=None, test=False):
		self.consts = rule.oblig["Constraints"].split('\n')[:-1] if not test else test
		self.rule_name = rule.oblig["rule_name"] if not test else 'TEST'
		self.errors = []

	def __str__(self):
		return etree.tostring(self.parse(), pretty_print=True, encoding='unicode')

	def cons_to_element(self):
		return self.parse()

	def parse_var(self, var):
		if not check_simple(var):
			return 'full'
		if var[0].isalpha() and var[-1].isnumeric():
			return 'Var'
		else:
			return 'Ind'

	def divide_constraint(self, cons, sign=False, key='poeqijf'):
		assert sign != key
		if sign:
			fsign = '\\'+sign if sign in '+*' else sign
			s = '(?P<left>.+?)\s?{}\s?(?P<right>.+)'.format(fsign)
			r = re.compile(s, flags=re.MULTILINE)
		else:
			r = self.pat[key]
		if key in 'orand':
			return {'vars': ','.join(cons.split(' {} '.format(key)))}
		if key == "Sumproduct":
			return {'left': cons.split(sign)[0].strip(), 'right': cons.split(sign)[1].strip()}
		if sign == ">":
			return {'vars': ','.join(cons.split(' > ')), 'rel': 'GreaterThan'}
		match = [m.groupdict() for m in r.finditer(cons)]
		try:
			res = match[0]
		except Exception as e:
			print("divide_constraint match error; cons: {}, sign: {}, key {}, match: {}".format(cons,sign,key, match))
			raise ValueError
		try:
			assert len(match)==1
		except Exception as e:
			print('length of MATCH not equal one',res)
			raise e
		return res

	def scrutinize(self, cons):
		scrut_dic = {}
		if '{' in cons:
			scrut_dic['set'] = True
		if ' ' not in cons or '>' in cons:
			scrut_dic['rel'] = True
		if bool(self.pat['opr'].match(cons)):
			scrut_dic['fun'] = True
		if 'exists' in cons:
			scrut_dic['exs'] = True
		if 'or ' in cons:
			scrut_dic['or'] = True
		if 'and ' in cons:
			scrut_dic['and'] = True
		if 'in ' in cons:
			scrut_dic['in'] = True
		if '=' in cons:
			scrut_dic['='] = True	
		return scrut_dic

	def parse_flow(self, cons):
		scrut_dic = self.scrutinize(cons)
		cons = cons[2:-1] if cons.startswith('~') else cons
		not_smp = len(scrut_dic)>1
		if not_smp:
			# or, and are parsed first
			if 'or' in scrut_dic.keys() or 'and' in scrut_dic.keys():
				name='or'
				return ('Or',self.divide_constraint(cons, key=name))
			#in lemma(X7) \in {SO, TOO, ALSO}
			if 'in' in scrut_dic.keys():
				name='in'
				return ('isIn',self.divide_constraint(cons, key=name))
			if '=' in scrut_dic.keys():
				return ('Equal',self.divide_constraint(cons, key='eq'))
			#UE
			name='rel'
			return (name,self.divide_constraint(cons, key=name)) if '>' not in cons else (name,self.divide_constraint(cons, sign='>', key=name))
		#simple: adj(X1)
		elif 'or' in scrut_dic.keys():
			name='or'
			return ('Or',self.divide_constraint(cons, key=name))
		elif 'exs' in scrut_dic.keys():
			name='exs'
			return ('Exists',self.divide_constraint(cons, key=name))
		elif 'rel' in scrut_dic.keys():
			name='rel'
			return (name,self.divide_constraint(cons, key=name)) if '>' not in cons else (name,self.divide_constraint(cons, sign='>', key=name))
		elif 'fun' in scrut_dic.keys():
			name = None
			if '=' in cons:
				name = 'Equal'
				return (name,self.divide_constraint(cons, key='fun'))
			elif '+' in cons:
				name = 'Sum'
				return (name,self.divide_constraint(cons, sign='+'))
			elif '*' in cons:
				name = 'product'
				return (name,self.divide_constraint(cons, sign='*'))
			else:
				raise KeyError
		else:
			return ['error',{}]

	def make_node(self, parent, rawcons, discr="Rel"):
		cons = preprocess(rawcons)
		try:
			scr = self.parse_flow(cons)
			name, elem = scr[0], scr[1]
		except Exception as e:
			name = 'alone'
		res = parent
		if cons.startswith('~'):
			parent = etree.SubElement(res, "Neg")
		if name in 'isInrel':
			if discr == "Rel":
				atom = etree.SubElement(parent, "Atom")
				atom.append(etree.Comment(rawcons))
			else:
				assert discr == "Fun"
				atom = parent
			rel = etree.SubElement(atom, discr)
			try:
				rel.text = elem[name] if name=='rel' else name
			except Exception as e:
				print('REL PROBLEMS {} {} {}'.format(elem, name, cons))
			where = atom
			vrs = (elem.get('vars'), 'vars')
			vrs = (elem.get('set'), 'set') if vrs[0] is None else vrs
			if 'set' in vrs:
				expr = etree.SubElement(atom, 'Expr')
				exp_node = self.make_node(expr, elem['expr'], discr='Fun')
			if '{' in vrs[0]:
				set_node = etree.SubElement(atom, 'Expr')
				f_node = etree.SubElement(set_node, 'Fun')
				f_node.text = 'set'
				where = set_node
				elem[vrs[1]] = elem[vrs[1]][1:-1]
			for v in elem.get(vrs[1]).split(','):
				v = v.strip()
				var = self.parse_var(v)
				if var == 'full':
					add = self.make_node(etree.SubElement(where, 'Expr'), v, 'Fun')
				else:
					var_node = etree.SubElement(where, var)
					var_node.text = v
			return res
		elif name in 'EqualExistsSumproduct':
			upper = parent if name in 'Sumproduct' else etree.SubElement(parent, name)
			upper.append(etree.Comment(rawcons))
			if name in 'Sumproduct':
				func_node = etree.SubElement(upper, 'Fun')
				func_node.text = 'sum' if name=='Sum' else 'product'
			for el in sorted(elem.keys()):
				add_parent = upper
				if name in 'EqualSumproduct':
					add_parent = etree.SubElement(upper, 'Expr') if not check_simple(elem[el]) else add_parent
					try:
						add = self.make_node(add_parent, elem[el], discr='Fun')
					except ValueError as e:
						print('I have an error in adding {}\nel: {}\ncons: {}'.format(name,elem[el],cons))
						pass
				elif name=='Exists':
					add = self.make_node(add_parent, elem[el])
			return res
		elif name in 'AndOr':
			upper = etree.SubElement(parent, name)
			upper.append(etree.Comment(rawcons))
			pat = r',\s*(?![^()]*\))'
			for var in re.split(pat, elem['vars']):
				add = self.make_node(upper, var)
			return res
		elif ' ' not in cons:
			var = self.parse_var(cons)
			var_node = etree.SubElement(parent, var)
			var_node.text = cons
			return res
		else:
			print('\nWHOA! NIEZNANY WIĄZ', cons, discr, name, elem)
			raise ValueError

	def parse(self):
		# xml version
		root = etree.Element("constraints")

		for c in self.consts:
			if c.startswith('<') or c.startswith('  '):
				self.errors.append((self.rule_name, c))
				continue
			try:
				parent = etree.Element("formula")
				node_to_add = self.make_node(parent, c)
				root.append(node_to_add)
			except Exception as e:
				print('CONS MODULE ERROR; CONSTRAINT NOT CAUGHT!: {} {}'.format(self.rule_name, c))
				self.errors.append((self.rule_name, c))
				print(e)
				unknw = etree.SubElement(root, 'unknown')
				unknw.text = c
		return root
