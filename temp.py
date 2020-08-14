import random
import os
MR_TRIALS = 100

def is_prime(n):
	""" checks if a number is probably prime using MR_TRIALS number of Miller-Rabin tests. """
	""" clearly polynomial """
	if n<2:
		return False
	if n == 2 or n == 3:
		return True
	r = 0
	d = n-1
	while d%2 == 0:
		d /= 2
		r += 1

	for _ in range(MR_TRIALS):
		a = pow(random.randint(2,n-1),d,n)
		if a == 1 or a == n-1:
			continue
		f = 0
		for i in range(r-1):
			a = a*a %n
			if a == n-1:
				f = 1
				break
		if f == 0:
			return False
	return True
def getrandprime(n):
	""" gets random odd prime having n bits """
	""" expected runtime O(n) as a consequence of the prime number theorem """
	if n == 2:
		return 3
	while 1:
		p = (1<<(n-1)) + random.getrandbits(n-2)*2 + 1
		if is_prime(p):
			return p
def generate_cyclic(n):
	""" generates a safe prime p having n bits and a generator of Zp* """
	""" no known bound for runtime """

	# q = nxt_prime(random.getrandbits(n))
	while 1:
		q = getrandprime(n-1)
		if not is_prime(2*q + 1):
			continue
		p = 2*q + 1
		while 1:
			g = random.randint(1, p-1)
			if pow(g,2,p) != 1 and pow(g,q,p) != 1:
				return (g,p)
def gen(seed, n):
	random.seed(seed)					# seed used to get consistent results accross runs
	g, p = generate_cyclic(n)			# prime p and generator g of Zp*
	x = random.randint(0, p-2)			# part of private key
	y = pow(g,x,p)						# corresponding part of public key

	z = random.randint(1,p-1)			# random member of Zp* used for hashing 
	in_size = 2*( (p-1).bit_length()-1) # input size for hash function
	out_size = (p-1).bit_length()		# output size for hash function

	s = (g,p,z,in_size,out_size)		# key for hash

	pub = (g,p,y)
	priv = (g,p,x)
	return (pub,priv,s)

class Hasher:
	def __init__(self, s):
		self.s = s
	def hash(self, m):
		""" 
		collision resistant hash function from Z_{p-1}^2 -> Z_p* 
		or equivalently {0,1}^in_size -> {0,1}^out_size
		"""
		g,p,z,in_size,out_size = self.s
		x = m>>(in_size/2)
		y = m - (x << (in_size/2))

		return (pow(g,x,p) * pow(z,y,p)) %p
	def Hash(self, m):
		""" 
		uses Merkle-Damgard transform to generate hash
		function form {0,1}* -> Zp*
		"""
		g,p,z,in_size,out_size = self.s
		block_size = in_size - out_size
		blocks = []
		while 1:
			blocks.append(m%(1<<block_size))
			m >>= block_size
			if m == 0:
				break
		return reduce(lambda x, y: hash((y<<out_size) + x), [0] + blocks)

class Elgamal:
	def encrypt(self, pub, m):
		g,p,gx = pub
		assert 0 <= m < p
		r = random.randint(1, p-1)

		return (pow(g,r,p), m*pow(gx,r,p) %p)
	def decrypt(self, priv, m):
		g,p,x = priv
		gr, ms = m
		s = pow(gr, x, p)

		return ms*pow(s, p-2, p) %p

class Signer:
	def __init__(self, s):
		self.hasher = Hasher(s)
	def sign(self, m, priv):
		# print m
		g,p,x = priv
		r = random.randint(0, p-2)
		t = pow(g,r,p)
		c = self.hasher.Hash((m<<t.bit_length()) + t)

		# if c < 0:
		# 	print "NLLA", (m<<t.bit_length()) + t

		return (((c*x + r)%(p-1))<<p.bit_length()) + t
	def verify(self, m, pub, sgn):
		g,p,y = pub
		z,t = sgn>>(p.bit_length()), sgn%(1 << p.bit_length())

		# print m
		# print self.hasher.Hash((m<<t.bit_length()) + t)
		return pow(g,z,p) == pow(y, self.hasher.Hash((m<<t.bit_length()) + t)%(p-1) ,p)*t %p

class FaultTolerator:
	def __init__(self, n, k, s):
		self.n = n
		self.k = k
		self.signer = Signer(s)
	def lagrange_interpolation(self, known_points, unknown_x_coord, p):
		values = []
		for x in unknown_x_coord:
			value = 0
			for i in range(len(known_points)):
				xi, yi = known_points[i]
				product = yi
				for j in range(len(known_points)):
					if i == j:
						continue
					xj, yj = known_points[j]
					product = product*(x - xj)*pow(xi - xj, p-2, p) %p
				value = (value + product)%p
			values.append(value)
		return values
	def encode(self, blocks, priv, tag_priv):
		g,p,x = priv
		points = [(pow(g,i+1,p), blocks[i]) for i in range(self.k)]
		encoded = blocks + self.lagrange_interpolation(points, [pow(g,i,p) for i in range(self.k+1,self.n+1)], p)
		return map(lambda x: (x<<(2*tag_priv[1].bit_length())) + self.signer.sign(x, tag_priv), encoded)
		# return map(lambda x: (x, sign(x, priv)) , encoded)
	def recover(self, encoded_blocks, pub, tag_pub):
		g,p,y = pub
		uncorrupted = []
		for i in range(1,self.n+1):
			m = encoded_blocks[i-1]>>(2 * tag_pub[1].bit_length())
			t = encoded_blocks[i-1] - (m<<(2 * tag_pub[1].bit_length()))
			# m, t = encoded_blocks[i-1]
			if self.signer.verify(m, tag_pub, t):
				uncorrupted.append( (pow(g,i,p), m) )
		if len(uncorrupted) < self.k:
			print "Error: More than {} corrupted".format(self.n - self.k)
			return None
		return self.lagrange_interpolation(uncorrupted[:self.k], [pow(g,i,p) for i in range(1,self.k+1)], p)

def stringToInt(s):
	return int(s.encode('hex'), 16)

def intToString(n):
	s = ""
	while n:
		s += chr(n%256)
		n >>= 8
	return s[::-1]

class Connection:
	def __init__(self, r=0, w=1):
		self.r = r
		self.w = w
	def send(self, x, numbits):
		# print "sending",x
		for i in range(numbits/8):
			os.write( self.w, chr(x%256) )
			x >>= 8
	def recv(self, numbits):
		s = ""
		while len(s) < numbits/8:
			s += os.read(self.r, 1)
		# print "received", stringToInt( s[::-1] )
		if random.random() < 0.1:
			return random.getrandbits(8*len(s))
		return stringToInt( s[::-1] )
		# return s[::-1]

class FaultTolerantConnection:
	def __init__(self, n, k, send_con, recv_con, block_size, tag_size, s):
		self.n = n
		self.k = k
		self.ft = FaultTolerator(n, k, s)
		self.send_con = send_con
		self.recv_con = recv_con
		self.block_size = block_size
		self.tag_size = tag_size
	def send(self, x, priv, tag_priv):
		x = stringToInt(repr(x))
		# print "sending", x
		blocks = []
		while 1:
			blocks.append(x%(1<<(self.block_size - 1)))
			x >>= self.block_size - 1
			if x == 0:
				break
		while len(blocks)% self.k:
			blocks.append(0)
		# print "sending", blocks
		for i in range(self.k):
			blocks.append(0)

		for i in range(0, len(blocks), self.k):

			# print "sending", blocks[i:i+self.k]
			for j, block in enumerate( self.ft.encode( blocks[i:i+self.k], priv, tag_priv ) ):
				# print block.bit_length(), self.block_size + self.tag_size
				self.send_con[j].send(block, self.block_size + self.tag_size)
	def recv(self, pub, tag_pub):
		a = []
		while 1:
			encoded_blocks = []
			for j in range(self.n):
				encoded_blocks.append( self.recv_con[j].recv(self.block_size + self.tag_size) )
			# print "received", encoded_blocks
			# print "recovered", self.ft.recover(encoded_blocks, pub, tag_pub)
			temp = self.ft.recover(encoded_blocks, pub, tag_pub)
			if temp == [0 for i in range(self.k)]:
				# print "received whole block"
				break
			a += temp
		# print "received", a
		a = reduce( lambda x, y: (x<<(self.block_size - 1)) + y, a[::-1])
		# print "received", a
		a = intToString(a)
		# print a
		return eval(a)


# n = 16
# e = 4
# k = n - e

# block_size = 64
# tag_security = 64
# tag_size = 2*tag_security

# a_pub, a_priv, a_s = gen(69420, block_size)
# b_pub, b_priv, b_s = gen(42069, block_size)
# sign_pub, sign_priv, sign_s = gen(0, tag_security)
# s = sign_s