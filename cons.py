# -*- coding: utf-8 -*-

import Kubas_module.Rule as rl
import lxml.etree as etree
import re

#This Class takes a rule and parses it in order to obtain an XML <contraints> node
class Constraints_Node(object):

	signs = '=+>~'
	patterns = {
	"rel": "(?P<rel>^\w+)\((?P<vars>.+)\)$",
	'in': "(?P<expr>^.+)\s.*in (?P<set>{.+})$",
	'fun': "(?P<left>.+?) *[=>] *(?P<right>.+)",
	'exs': ".+exists (?P<var>.+) (?P<expr>.+)",
	'or': "(?P<vars>.+) or .+",
	'neg' : "~\((?P<neg>.+)\)",
	'opr' : ".+[>\+=].+",
	'Sum' : ".+"

	# bezpieczniej by było unikać ".+" i ".*" np.
	#       "(?P<fname>[\w_]+)\(.+?\) *= *(?P<rfside>.+)" JK
	# a że "_" się zalicza do "\w, to:"
	#       "(?P<fname>\w+)\(.+?\) *= *(?P<rfside>.+)" JK
	}	

	pat = {key:re.compile(value, flags=re.MULTILINE) for (key,value) in patterns.items()}

	def __init__(self, rule=None, test=False):
		self.consts = rule.oblig["Constraints"].split('\n')[:-1] if not test else test
		self.rule_name = rule.oblig["rule_name"] if not test else 'TEST'
		self.errors = []
	# 'in ' := ' in '? JK
	# nie bo czasem jestjeszcze wersja '\in ' TT
	# 'atom' nigdy nie występuje w ręcznej regule JK

	def __str__(self):
		# nie znałem __str__, super JK
		return etree.tostring(self.parse(), pretty_print=True, encoding='unicode')

	def cons_to_element(self):
		return self.parse()

	def parse_var(self, var):
		if var.isalpha() or var.isnumeric():
			# so short JK
			return 'Ind'
		else:
			return 'Var'

	def divide_cstr(self, cons, sign=False, key=False):
		assert sign != key
		s = '(?P<left>.+) ?{} ?(?P<right>.+)'.format(sign) if sign else self.pat[key]
		r = re.compile(s, flags=re.MULTILINE) if sign else s
		if key in 'orand':
			return {'vars': ','.join(cons.split(' {} '.format(key)))}
		if key == "Sum":
			print('in..')
			return {'left': cons.split('+')[0].strip(), 'right': cons.split('+')[1].strip()}
		match = [m.groupdict() for m in r.finditer(cons)]
		# print(match)
		# print(key)
		# print(name)
		res = match[0]
		try:	
			assert len(match)==1
		except Exception as e:

			print('DŁUGI',res)
		return res

	def scrutinize(self, cons):
		scrut_dic = {}
		if '{' in cons:
			scrut_dic['set'] = True
		if ' ' not in cons:
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
		if cons.startswith('~'):
			return self.scrutinize(cons[2:-1])
		
		smp = len(scrut_dic)>1
		if smp:
			#in lemma(X7) \in {SO, TOO, ALSO}
			if 'in' in scrut_dic.keys():
				name='in'
				return ('isIn',self.divide_cstr(cons, key=name))
			if '=' in scrut_dic.keys():

				return ('Equal',self.divide_cstr(cons, key='fun'))
			#UE
			name='rel'
			return (name,self.divide_cstr(cons, key=name))
		#simple: adj(X1)	
		elif 'rel' in scrut_dic.keys():
			name='rel'
			return (name,self.divide_cstr(cons, key=name))
		elif 'fun' in scrut_dic.keys():
			name = None
			name = 'Equal' if '=' in cons else 'GreaterThan'
			name = 'Sum' if ('+' in cons and name is None) else name
			return (name,self.divide_cstr(cons, key='fun')) if name != 'Sum' else (name,self.divide_cstr(cons, sign='+'))
		elif 'exs' in scrut_dic.keys():
			name='exs'
			return ('Exists',self.divide_cstr(cons, key=name))
		elif 'or' in scrut_dic.keys():
			name='or'
			return ('Or',self.divide_cstr(cons, key=name))
		else:
			# print('CORNER CASE: ', cons, scrut_dic)
			return ['unknwn',{}]
			
		

	def make_node(self, parent, cons, discr="Rel"):
		try:
			scr = self.scrutinize(cons)
			name, elem = scr[0], scr[1]
		except Exception as e:
			# print('ERR: ', cons)
			name = 'alone'

		res = parent
		if cons.startswith('~'):
			parent = etree.SubElement(res, "Neg")
			# tu brakuje jeszcze czegoś z komentarzem
		atom_check = 'isInrel'
		if name in atom_check:
			if discr == "Rel":
				atom = etree.SubElement(parent, "Atom")
				atom.append(etree.Comment(cons))
			else:
				assert discr == "Fun"
				atom = parent

			rel = etree.SubElement(atom, discr)
			rel.text = elem[name] if name=='rel' else name
			
			where = atom

			vrs = (elem.get('vars'), 'vars')
			vrs = (elem.get('set'), 'set') if vrs[0] is None else vrs
			if '{' in vrs[0]:
				set_node = etree.SubElement(atom, 'Set')
				where = set_node
				elem[vrs[1]] = elem[vrs[1]][1:-1]
			for v in elem.get(vrs[1]).split(','):
				v = v.strip()
				var = self.parse_var(v)
				var_node = etree.SubElement(where, var)
				var_node.text = v
			if 'set' in vrs:
				expr = etree.SubElement(atom, 'Expr')
				exp_node = self.make_node(expr, elem['expr'], discr='Fun')
				# print(exp_node)

			return res
		elif name in 'EqualExistsGreaterThanSum':
			upper = etree.SubElement(parent, name)
			upper.append(etree.Comment(cons))
			for el in sorted(elem.keys()):
				add_parent = upper
				if name in 'EqualGreaterThanSum':
					add_parent = etree.SubElement(upper, 'Expr') if not elem[el].isalnum() else add_parent
					try:
						add = self.make_node(add_parent, elem[el], discr='Fun')
					except ValueError as e:
						pass
						# print('BUUUKKA')
						# print(elem, elem[el])
				elif name=='Exists':
					add = self.make_node(add_parent, elem[el])
			return res
		elif name in 'AndOr':
			upper = etree.SubElement(parent, name)  
			upper.append(etree.Comment(cons))
			for var in elem['vars'].split(','):
				# expr = etree.SubElement(parent, self.scrutinize(var)[0])
				add = self.make_node(upper, var)
			return res
		elif cons.isalnum():
			var = self.parse_var(cons)			
			var_node = etree.SubElement(parent, var)
			var_node.text = cons
			return res
		else:
			# print(cons, discr)
			raise ValueError

	def parse(self):
		# xml version
		root = etree.Element("Constraints")

		for c in self.consts:
			if c.startswith('<') or c.startswith('  '):
				self.errors.append((self.rule_name, c))
				continue
			try:
				root = self.make_node(root, c)
			except Exception as e:
				# print('EXCEPT !!!', self.rule_name)
				# print('NOT CAUGHT!: {}'.format(c))
				self.errors.append((self.rule_name, c))
				unknw = etree.SubElement(root, 'unknown')
				unknw.text = c
	

		return root

			