import os, random

random.seed(1)
n = 16

cons = []

for i in range(2*n):
	cons.append( os.pipe() )

pid1 = os.fork()
if pid1 == 0:
	# child1
	os.system("python OT_data.py " + ' '.join( map(str, [ x[0] for x in cons[:n] ] + [ x[1] for x in cons[n:] ] ) ) )
else:
	pid2 = os.fork()
	if pid2 == 0:
		# child2
		os.system("python OT_index.py " + ' '.join( map(str, [ x[0] for x in cons[n:] ] + [ x[1] for x in cons[:n] ] ) ) )
	else:
		pass