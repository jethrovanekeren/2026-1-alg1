

# This function determines the naive possible values of n_p for N
# Using Sylow's 3rd theorem
def np(N, p):
    F = list(factor(N))
    m = [x for x in F if x[0] == p][0][1]
    b = N / p^m
    
    b_divs = divisors(b)
    nplist = [x for x in b_divs if mod(x, p) == 1]
    
    return nplist

# This function outputs all the lists of possible values of np
# for each prime dividing N
def allnp(N):
    pf = prime_divisors(N)
    
    return [np(N, p) for p in pf]

def allnp_withp(N):
    pf = prime_divisors(N)
    
    return [[p, np(N, p)] for p in pf]

def printallnp(N):
    pf = prime_divisors(N)
    print('N = ', N, ' =', factor(N))
    
    for p in pf:
        L = np(N, p)
        print(p, ": n_p can be", L)
    
    return []

# This is the simplest test:
# See if one of the sets of n_p has cardinality 1
def test1(N):
    nps = allnp(N)
    exists_normal = any([len(x) == 1 for x in nps])
    return exists_normal

# print('Using test1: the naive count of n_p for each prime divisor p of N')
# for N in range(2,300):
#     if not(test1(N)):
#         printallnp(N)
    


# The idea for this test is that if one of the max n_p's is small relative to the size of G, then the map G --> S_n might be forced to have nontrivial kernel   
def test2(N):
    exists_normal = any([N > factorial(max(x)) for x in allnp(N)])
    
    return exists_normal

# print('\n\n\n')
# print('Using test2: the idea that (n_p)! < N implies a homo with kernel G --> S_n for n = n_p')
# for N in range(2,300):
#     if not(test2(N)):
#         printallnp(N)
    
    

def test3(N):
    exists_normal = False
    
    if test1(N):
        exists_normal = True
        return exists_normal
    
    # If we are here
    # we can be sure all the n_p-lists contain an element larger than 1
       
    F = list(factor(N))
    
    # We want all the primes that divide N with multiplicity 1
    simple_primes = [pair[0] for pair in F if pair[1] == 1]
       
    # We run through prime divisors p of N
    # consider a p-Sylow - it has p^m elements
    # Gather all elements of q-Sylows for simple primes q different than p
    # See if the total is >= N. If so we win
    for pair in list(factor(N)):
        p = pair[0]
        m = pair[1]
        
        chunks = [min(np(N, q)[1:])*(q-1) for q in simple_primes if q != p]
        nonp = sum(chunks)
        
        if nonp + p^m >= N:
            exists_normal = True

    return exists_normal    
    

def test3verbose(N):
    exists_normal = False
    
    if test1(N):
        exists_normal = True
        return exists_normal
    
    # If we are here
    # we can be sure all the n_p-lists contain an element larger than 1
       
    F = list(factor(N))
    
    # We want all the primes that divide N with multiplicity 1
    simple_primes = [pair[0] for pair in F if pair[1] == 1]
       
    # We run through prime divisors p of N
    # consider a p-Sylow - it has p^m elements
    # Gather all elements of q-Sylows for simple primes q different than p
    # See if the total is >= N. If so we win
    for pair in list(factor(N)):
        p = pair[0]
        m = pair[1]
        
        chunks = [min(np(N, q)[1:])*(q-1) for q in simple_primes if q != p]
        nonp = sum(chunks)
        
        print('For', p, ': non-p + p^m = ', nonp, '+', p^m, '=', nonp + p^m)
        if nonp + p^m >= N:
            exists_normal = True
            print('Therefore not simple')

    return exists_normal      
    
    

  
    
    
# The idea for this test is that if G is forced to have a homomorphism to A_n but N does not divide the order of A_n then we win   
def test4(N):
    exists_normal = any([mod(factorial(max(x))/2, N) != 0 for x in allnp(N)])
    
    return exists_normal    
    

# A small variation on test4
# The idea here is that if G is forced to have a homomorphism to A_n, and An is simple (so n >= 5) and #An / #G = k where k < n, then an action of An on a k-element set appears, but this is impossible but N does not divide the order of A_n then we win   
def test4prime(N):
    exists_normal = any([max(x) >= 5 and factorial(max(x))/(2*N) < max(x) for x in allnp(N)])
    
    return exists_normal       
   
    
    
    
    
# Now we wish to show Sylows have trivial intersection, in order to strengthen the 'clash argument'

# This function excludes small possibilities for n_p
# Returns True if np is 'small'
def small_np_excluder(N, p, np):
    
    if factorial(np)/2 < N:
        return True
    
    if np >= 5 and floor(factorial(np)/(2*N)) < np:
        return True
    
    return False

# Example: N = 180
# [(x[0], [small_np_excluder(180, x[0], y) for y in x[1]]) for x in allnp_withp(180)]
# [(2, [True, True, True, False, False, False]),
#  (3, [True, True, False]),
#  (5, [True, True, False])]



# TO DO : REFINE THIS COUNT USING SIMPLICITY OF AN

# this function determines for which p | N we can guarantee the p-Sylows of order p^2 actually have mutually trivial intersection
def repeling_Sylows(N):   
    F = list(factor(N))
    psquares = [x[0] for x in F if x[1] == 2]
    
    rs = []
    
    # If two distinct p-Sylows had nontrivial intersection I, it would have size p, and
    # the normaliser N_G(I) would contain both the p-Sylows in it, and so have size at least p^3
    
    for p in psquares:
        
        # This is an upper bound on the index of N_G(I) in G
        NGI_bound = floor(N/p^3)
        
        # In this case G acting on the cosets of N_G(I) gives a homo into a small A_n
        if factorial(NGI_bound)/2 < N:
            rs = rs + [p]
        
        # In this case G acting on the cosets of N_G(I) gives a homo into a medium-sized A_n
        # More precisely G can inject into the A_n in question, but it will have a 'small index'
        # Meaning that A_n would acquire an action on a set of size smaller than n, which contradicts simplicity of A_n
        if factorial(NGI_bound)/(2*N) < NGI_bound and NGI_bound >= 5:
            rs = rs + [p]
    
    return rs
    
# Let q be any prime divisor of N    
def findclash(N, q):
    F = list(factor(N))
    total = 0
    
    rs = repeling_Sylows(N)
    for p in [p for p in rs if p != q]:
        nps = np(N, p)
        # Assume np > 1
        # But if np is too small then the action of G on the set of p-Sylows gives a homo to a small S_n
        big_nps = [x for x in nps if not(small_np_excluder(N, p, x))]
        n = min(big_nps)
        print(n)
        total = total + n*(p^2-1)
    
    ppure = [x[0] for x in F if x[1] == 1]
    for p in [p for p in ppure if p != q]:
        nps = np(N, p)
        # Assume np > 1
        # But if np is too small then the action of G on the set of p-Sylows gives a homo to a small S_n
        big_nps = [x for x in nps if not(small_np_excluder(N, p, x))]
        n = min(big_nps)
        print(n)
        total = total + n*(p-1)        
    
    # We check if all the above is enough to force a unique q-Sylow
    m = [x[1] for x in F if x[0] == q][0]
    
    # If there are so many elements that a unique q-Sylow is forced, then return True
    if total + q^m >= N:
        return True
    
    return False

def test5(N):
    F = list(factor(N))
    
    for q in [x[0] for x in F]:
        if findclash(N, q):
            print('There has to be a unique p-Sylow, where p = ', q)
            ppure = [x[0] for x in F if x[1] == 1 and x[0] != q]
            rs = [p for p in repeling_Sylows(N) if p != q]
            
            print('Indeed the following primes occur with multiplicity 1')
            print([[p, 'with n_p:', np(N, p)] for p in ppure])
            print('The primes with multiplicity 2, and repelling Sylows are:')
            print([[p, 'with n_p:', np(N, p)] for p in rs])
            
            return True

    return False    
    
#print('\n\n\n')
#print('Using clash of numbers of elements of different orders')
#for N in range(2,300):
#    if not(test3(N)):
#        printallnp(N)    
    
    
    
print('\n\n\n')
print('Using test2, then tes3: the clash of numbers of elements of different orders')
for N in range(2,300):
    if not(test1(N)) and not(test2(N)) and not(test3(N)) and not(test4(N)) and not(test4prime(N)):
        printallnp(N)     
    
    
    
    
    
    
    
    
    
    
    
# This function is for LATEX display of prime factorisation    
def Factoriser(N):
    def Exponent(m):
        if m == 1:
            return ''
        if m > 1:
            return '^' + str(m)
        
    F = list(factor(N))
    factored_form = ' \cdot '.join([str(pair[0]) + Exponent(pair[1]) for pair in F])
    
    return factored_form
    
    
def MechanicalSylow(N, verbose):
    
    out_string = ''.join(['\\section{Groups of order $', str(N), '$}\label{sec:order.', str(N), '} \n\n\n'])
    
    # If N = 1 then G is the trivial group
    if N == 1:
        out_string = ''.join([out_string] + ['A group of order $1$ is the trivial group $\\{e\\}$.\n\n'])
        
        if verbose == False:
             return ''
        
        if verbose == True:
             return out_string
    
    # If N is prime then G is the cyclic group Z/p
    if is_prime(N):
        out_string = ''.join([out_string] + ['The order is prime, and so the only group of this order is $\\mathbb{Z} / ', str(N), '$.\n\n'])
        
        if verbose == False:
             return ''
        
        if verbose == True:
             return out_string
        
    # Get the prime factorisation of N
    F = list(factor(N))
    out_string = ''.join([out_string] + ['The order factorises as $', str(N), ' = ', Factoriser(N), '$.\n\n'])
    
    # If N is prime power then G is not simple
    if len(F) == 1:
        p = F[0][0]
        m = F[0][1]
        out_string = ''.join([out_string] + ['The order $', str(N), ' = ', str(p), '^', str(m), '$ is a power of a prime, so $G$ contains normal subgroups. For example the centre of $G$ contains a copy of $\\mathbb{Z} / ', str(p), '$.\n\n'])
        
        if verbose == False:
             return ''
        
        if verbose == True:
             return out_string

    ##################
    # Run through the basic consequences of Sylow theory
    
    # N = pq
    if len(F) == 2 and F[0][1] == 1 and F[1][1] == 1:
       
        out_string = ''.join([out_string] + ['The order is of the form $p q$ for distinct primes $p$ and $q$, so $G$ contains a normal subgroup.\n\n'])
        
        if verbose == False:
             return ''
        
        if verbose == True:
             return out_string    

    # N = p^2q
    if len(F) == 2 and F[0][1] * F[1][1] == 2:
       
        out_string = ''.join([out_string] + ['The order is of the form $p^2 q$ for distinct primes $p$ and $q$, so $G$ contains a normal subgroup.\n\n'])
        
        if verbose == False:
             return ''
        
        if verbose == True:
             return out_string             
            
            
    # N = p^2q^2
    if len(F) == 2 and F[0][1] == 2 and F[1][1] == 2 and N != 36:
       
        out_string = ''.join([out_string] + ['The order is of the form $p^2 q^2$ for distinct primes $p$ and $q$, so $G$ contains a normal subgroup.\n\n'])
        
        if verbose == False:
             return ''
        
        if verbose == True:
             return out_string      
    
    # N = pqr
    if len(F) == 3 and F[0][1] == 1 and F[1][1] == 1 and F[2][1] == 1:
       
        out_string = ''.join([out_string] + ['The order is of the form $p q r$ for distinct primes $p$, $q$ and $r$, so $G$ contains a normal subgroup.\n\n'])
        
        if verbose == False:
             return ''
        
        if verbose == True:
             return out_string 
            
    ##################
    # Now finally we start doing some nontrivial tests
    
    # Compute the options for each n_p
    nps = allnp_withp(N)
    
    # We do test1 - Namely see if n_p = 1 mod p and n_p | b forces p = 1
    unique_nps = [x for x in nps if len(x[1]) == 1]
    exists_normal = (len(unique_nps) > 0)
    
    if exists_normal:
        first = unique_nps[0]
        p = first[0]
        m = [pair[1] for pair in F if pair[0] == p][0]
        b = N / p^m
        out_string = ''.join([out_string] + ['The number $n_{', str(p), '}$ of $', str(p), '$-Sylows is a divisor of $', str(b), '$, and satisfies $n_{', str(p), '} \\equiv 1 \\bmod{', str(p), '}$. Only $n_{', str(p), '} = 1$ satisfies these properties. Therefore there is a unique $', str(p), '$-Sylow, and it is a normal subgroup of $G$.'])
        
        return out_string
    
    # We do test2
    small_nps = [x for x in nps if N > factorial(max(x[1]))]
    exists_normal = (len(small_nps) > 0)
    
    if exists_normal:
        first = small_nps[0]
        p = first[0]
        m = [pair[1] for pair in F if pair[0] == p][0]
        b = N / p^m
        npmax = max(first[1])
        
        out_string = ''.join([out_string] + ['The number $n_{', str(p), '}$ of $', str(p), '$-Sylows is a divisor of $', str(b), '$, and satisfies $n_{', str(p), '} \\equiv 1 \\bmod{', str(p), '}$. The possible values of $n_p$ are ', ', '.join([str(x) for x in first[1]]), '. There is therefore a nontrivial homomorphism $\\varphi : G \\rightarrow S_{', str(npmax), '}$. But $\\# G > \\# S_{', str(npmax), '} = ', str(factorial(npmax)), '$, so $\\ker(\\varphi) \\neq \\{e\\}, G$ is a normal subgroup of $G$.' ])
        
        return out_string
    
    # We do test3
    
    simple_primes = [pair[0] for pair in F if pair[1] == 1]
    for pair in F:
        q = pair[0]
        m = pair[1]
        
        min_nps = [[p, min(np(N, p)[1:])] for p in simple_primes if q != p]
        chunks = [(p-1)*min(np(N, p)[1:]) for p in simple_primes if q != p]
        nonp = sum(chunks)
        
        if nonp + q^m >= N:
            simple_primes_not_q = [p for p in simple_primes if q != p]
            
            # Because of English tenses I phrase things differently depending how many primes there are
            if len(simple_primes_not_q) == 1:
                p = simple_primes_not_q[0]
                
                out_string = ''.join([out_string] + ['The prime $', str(p), '$ divides $', str(N), '$ with multiplicity one. If $n_{', str(p), '} > 1$ then $n_{', str(p), '} \\geq ', str(min_nps[0][1]), '$. The $', str(p), '$-Sylows each contain $', str(p-1), '$ elements of order $', str(p), '$, and so in total $G$ contains at least $', str(min_nps[0][1]), ' \\cdot ', str(p-1), ' = ', str(nonp), '$ elements of order not a power of $', str(q), '$. '])
            
            if len(simple_primes_not_q) > 1:
                out_string = ''.join([out_string] + ['The primes $p = ', ', '.join([str(x) for x in simple_primes_not_q]), '$ each divide $', str(N), '$ with multiplicity one. If $n_p > 1$ for all $p$ then for $p = ', ', '.join([str(x) for x in simple_primes_not_q]), '$ we have $n_p$ at least $', ', '.join([str(x[1]) for x in min_nps]), '$, respectively. For each such $p$, the $p$-Sylows each contain $p-1$ elements of order $p$, and so in total $G$ contains at least $', ' + '.join([str(x[1]) + ' \\cdot (' + str(x[0]) + '-1)' for x in min_nps]), ' = ', str(nonp), '$ elements of order not a power of $', str(q), '$. '])
            
            if nonp + q^m > N:
                nonpbig = ['Since $', str(nonp), ' + ', str(q), '^', str(m), ' > ', str(N), '$ we arrive at a contradiction. Therefore $G$ has a normal subgroup.']
                
            if nonp + q^m == N:
                nonpbig = ['Since $', str(nonp), ' + ', str(q), '^', str(m), ' = ', str(N), '$, we deduce that there is at most one ', str(q), '-Sylow, so $G$ has a normal subgroup.']    

            out_string = ''.join([out_string] + ['\n\n'] + nonpbig)    
            
            return out_string
    
    # We do test4
    nonAn_nps = [x for x in nps if mod(factorial(max(x[1]))/2, N)]
    exists_normal = (len(nonAn_nps) > 0)
    
    if exists_normal:
        first = nonAn_nps[0]
        p = first[0]
        m = [pair[1] for pair in F if pair[0] == p][0]
        b = N / p^m
        npmax = max(first[1])
        
        out_string = ''.join([out_string] + ['The number $n_{', str(p), '}$ of $', str(p), '$-Sylows is a divisor of $', str(b), '$, and satisfies $n_{', str(p), '} \\equiv 1 \\bmod{', str(p), '}$. The possible values of $n_p$ are ', ', '.join([str(x) for x in first[1]]), '. There is therefore a nontrivial homomorphism $\\varphi : G \\rightarrow S_{', str(npmax), '}$. If $G$ is to have no normal subgroup then in fact we must have $\\varphi(G) < A_{', str(npmax), '}$. But $N$ does not divide $\\# A_{', str(npmax), '} = ', str(factorial(npmax)/2), '$, so $G$ has a normal subgroup.' ])
        
        return out_string    
    
    # We do test4prime
    nonAn_nps = [x for x in nps if max(x[1]) >= 5 and factorial(max(x[1]))/(2*N) < max(x[1])]
    exists_normal = (len(nonAn_nps) > 0)
    
    if exists_normal:
        first = nonAn_nps[0]
        p = first[0]
        m = [pair[1] for pair in F if pair[0] == p][0]
        b = N / p^m
        npmax = max(first[1])
        
        out_string = ''.join([out_string] + ['The number $n_{', str(p), '}$ of $', str(p), '$-Sylows is a divisor of $', str(b), '$, and satisfies $n_{', str(p), '} \\equiv 1 \\bmod{', str(p), '}$. The possible values of $n_p$ are ', ', '.join([str(x) for x in first[1]]), '. There is therefore a nontrivial homomorphism $\\varphi : G \\rightarrow S_{', str(npmax), '}$. If $G$ is to have no normal subgroup then in fact we must have $\\varphi(G) < A_{', str(npmax), '}$. \n\n We see that $\\#A_{', str(npmax), '} / N = ', str(factorial(npmax)/(2*N)), ' < ', str(npmax), '$. But $A_{', str(npmax), '}$ is simple, while the action of $A_{', str(npmax), '}$ on the set of cosets of $G$ would induce a nontrivial homomorphism to the smaller group $S_{', str(factorial(npmax)/(2*N)), '}$. This contradiction shows that $G$ must have a normal subgroup.' ])
        
        return out_string    
    
    
    #######
    # If we got this far, then G might well be simple
    out_string = ''.join([out_string] + ['\n\n{\\color{red}As far as I can tell, there might be a simple group of this order.}'])
    
    
    return out_string


# verbose = True means list all order
# verbose = False means skip cases N = p^m, pq, p^2q, p^2q^2, pqr
def SylowList(Nmax, verbose):
    # Option 'w' so we are overwriting any contents in 'output.tex'
    with open('output.tex', 'w') as f:
            print('\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n\\usepackage{parskip}\n\\usepackage{color}\n\\usepackage[a4paper, margin=2.5cm]{geometry}\n\n\\begin{document}\n\n', file=f)
    
    for N in range(1,Nmax):
        s = MechanicalSylow(N, verbose)
        with open('output.tex', 'a') as f:
            print(s, file=f)
            print('\n\n', file=f)
    
    with open('output.tex', 'a') as f:
            print('\\end{document}', file=f)
    
    return []
    
    
    
    