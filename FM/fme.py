#!/usr/bin/python3
from io import StringIO
from subprocess import run, PIPE
from sympy import Symbol, Poly
import os
def remove_var(parameters, variables, inequalities):
	'''Removes variables from a INTEGER valued system (list)
		 of constraints using Fourier-Motzkin elimination process.

	- parameters: The symbols/variables that won't be eliminated
	- variables: The symbols/variables to be eliminated
	- list of polynomials, such that each polynomial P
		forms the constraint P >= 0

	= returns list of systems (lists) of constraints
		Two special cases of systems are:
		[]  = true  ( empty system )
		[-1]= false (-1 >= 0 )
	'''
	tmp = StringIO()
	print (f"{parameters} -> {variables}:", file=tmp)
	front = ''
	for ine in inequalities:
		print (f"{front} {ine} >= 0", file=tmp)
		front = '&'
	print (';', file=tmp)

	str = tmp.getvalue().replace("**", "^")

	proc = run([os.path.dirname(os.path.abspath(__file__)) + "/Simplifier"], stdout=PIPE, stderr=PIPE, input=str, universal_newlines=True)
	if proc.returncode != 0:
		print("Error running the Simplifier")
		print("==================")
		print(f"Return code: {proc.returncode}")
		print("==================")
		print(f"Stderr: {proc.stderr}")
		print("==================")
		print(f"Stdout: {proc.stdout}")
		raise Exception(f'Simplifier exited with error {proc.returncode}')

	#print(proc.stdout)	
	systems = proc.stdout.replace("^", "**").replace(" ","").replace("\n", "").split(';')

	out = []

	for system in systems:
		system = system.split(':', 1)[-1]
		if len(system) == 0:
			continue;

		constraints = system.split('&')
		for constraint in constraints:
			#print (constraint)
			l = []
			if len(constraint) == 0:
				continue

			if constraint == "true":
				continue

			if constraint == "false":
				l.clear()
				l.append(-1)
				break

			lhs = constraint[0:-3]
			rhs = constraint[-3:]
			#print(lhs)
			l.append(eval(f"Poly({lhs})"))
			if rhs == "==0":
				l.append(eval(f"Poly(-({lhs}))"))
		out.append(l)
	#print(out)
	return out
