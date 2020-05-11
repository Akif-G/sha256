"""
* Filename:   sha256.py
* Author:     Akif-G (mehmetgultekin  At  sabanciuniv.edu)
* Copyright:
* Disclaimer: This code is presented "as is" without any guarantees.
* Details:    Implementation of the SHA-256 hashing algorithm.
              SHA-256 is one of the three algorithms in the SHA2
              specification. The others, SHA-384 and SHA-512, are not
              offered in this implementation.
              For a better vision; Algorithm specification can be found here:
               * http://csrc.nist.gov/publications/fips/fips180-2/fips180-2withchangenotice.pdf 
              with some explanation:
               * https://tools.ietf.org/html/rfc4634#section-6.2

              Used Wikipedia as a source Of Pseudocode :
               * https://en.wikipedia.org/wiki/SHA-2#Pseudocode

              Block size:512 bit
              Output size: 256 bit
             
              ! note: this algorithm is known as susceptible for Length extension attack
                    : This attack is valid when the data and resulting signiture,that is computed with a secret key, is known while secretkey -salt- is not known. In vulnerable databases' with secret validation methods, attacker can use this algorithm, which is also aimed to be implemented in this repository.
                    : For more                    
                      * https://en.wikipedia.org/wiki/Length_extension_attack
                      * https://blog.skullsecurity.org/2012/everything-you-need-to-know-about-hash-length-extension-attacks
"""

### Useful functions for bit/byte/binary/decimal/hexadecimal operations  ###
def convertToBites(string):
    # not a part of the hashing algorithm but we will store and use bite string for explanation ease. 
    # so here to convert the strings into bitearray
    # note: we may use a function but i need every step shown on the output here...
    en=string.encode()
    arr=[]
    for i in en:
        arr.append(i)
    return arr

def wordConverter(arrayOfElems):
    # not a part of the hashing algorithm but we will store and use bite string for explanation ease. 
    #takes 4 8-bit and converts to 32 bits.
    collided=0
    for elem in arrayOfElems:
      #print("\te:",elem)
      collided=collided*(2**8)+elem
      #print("\t\t->",bin(elem),"\t->:",bin(collided))
    #print("c:",collided)
    return collided

def Lengthwith64bit(Length):
    # not a part of the hashing algorithm but we will store and use bite string for explanation ease. 
    # converts the Length to 64 bit representation, 
    # return will be 8 integer since we did not use 32(digest_size) for this far.
    arr=[0 for x in range(64)]
    inbits=bin(Length)[2:] #-2 is for 0b part since we are trying to count the bits.
    if len(inbits)>2**64:
        raise ValueError('value is bigger than 2**64')
    i=len(inbits)-1
    while i>=0:
        arr[63-i]=inbits[len(inbits)-1-i]
        i-=1
    #print(arr)
    #collide into 8 bites:
    asBin=""
    asHex=[]
    for j in range(64):
        if (j+1)%8!=0:
            asBin+=str(arr[j])
        else:
            asBin+=str(arr[j])
            asHex.append(asBin)
            asBin=""
    #convert from binary to integer -8 bit...
    asDec=[]
    for string in asHex:
        asDec.append(int(string,2))
    #print(asDec)
    return asDec



###          MACRO FUNCTIONS            ####

# these functions are going to be used in hashing process. They are not a part of the Hashing algorithm, but Can be assumed as core elements of Sha256 
block_size = 64
digest_size = 32

def CH(x,y,z):
    # choose( x, y, z) = (x AND y) XOR ( (NOT x) AND z)
    # for each bit index, that result bit is according to the majority of the 3 inputs bits for x y and z at this index.
    return (x & y ^( (~x) & z ) )

def MAJ( x, y, z):
    # majority( x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z)
    # as the x input chooses if the output is from y or from z. More precisely, for each bit index, that result bit is according to the bit from y (or respectively z ) at this index, depending on if the bit from x at this index is 1 (or respectively 0).
    return (x & y) ^ (x & z) ^ (y & z)

def ROTR(n,x):
    # rotateRight(n,x)=(x >> n) v (x << w - n). where w is digest_size  
    # equivalent to a circular shift (rotation) of x by n positions to the right. 
    try:
        return (x>>n) | (x<<(32-n)) & 0xFFFFFFFF #32=digest_size can be implemented as an input vice versa
    except:
        raise ValueError( 'n should be less than 32 in sha256 for RotateRight %s()'%(n))

def SHR(n,x):
    # SHR^n(x) = x>>n
    # The right shift operation SHR^n(x), where x is a w-bit (digest_size) word and n is an integer with 0 <= n < w.
    try:
        return (x>>n)
    except:
        raise ValueError('n should be less than 32 in sha256 for RotateRight %s()'%(n))

def BSIG0(x):
    # BSIG0(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x)
    return ROTR(2,x) ^ROTR(13,x)^ROTR(22,x)

def BSIG1(x):
    # BSIG1(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x)
    return ROTR(6,x) ^ROTR(11,x)^ROTR(25,x)

def SSIG0(x):
    # SSIG0(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x)
    return ROTR(7,x) ^ROTR(18,x)^SHR(3,x)

def SSIG1(x):
    # SSIG1(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x)
    return ROTR(17,x) ^ROTR(19,x)^SHR(10,x)



class Sha256:
    """
    algorithm can be defined in two stages:
        preprocessing:
            Preprocessing involves padding a message, parsing the padded message into m-bit blocks, and setting initialization values to be used in the hash computation. 
        
        hash computation:
            The hash computation generates a message schedule from the padded message and uses that schedule, along with functions, constants, and word operations to iteratively generate a series of hash values.
    """

    ###         PreProcessing           ###

    def __init__(self, message, salt=None):
        if message is not None:
            if type(message) is not str:
                raise TypeError('%s() argument 1 must be string, not %s' % (self.__class__.__name__, type(message).__name__))

        # Timeline of the processes:
        padded=self.padding(message,salt)
        #print("pad:",padded)
        parsed=self.parsing(padded)
        #print(parsed)

        ##
        ##

        #Constants and H(0) : will be used in Hash Processing.
        #these can not be changed, offered by NSA: 
        """ 
        constants: These words represent the first thirty-two bits of the fractional parts of the cube roots of the first sixtyfour prime numbers,in hex. See below:
        
        primes:
            2	3	5	7	11	13	17	19	23	29	31	37	41	43	47	53	59	61	67	71
            73	79	83	89	97	101	103	107	109	113	127	131	137	139	149	151	157	163	167	173
            179	181	191	193	197	199	211	223	227	229	233	239	241	251	257	263	269	271	277	281
            283	293	307	311  
        """
        self._K = [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
                    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
                    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
                    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
                    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
                    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
                    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
                    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
                    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
                    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
                    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
                    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
                    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
                    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
                    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
                    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

        """
        For SHA-256, the initial hash value, H(0), consists of the following eight 32-bit words, in hex.  These words were obtained by taking the first thirty-two bits of the fractional parts of the square roots of the first eight prime numbers.
        primes:
            2	3	5	7	11	13	17	19
        """

        self.initialHashValues = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
                0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
        ##
        ##

        self.sha256=self.hash(parsed)

    def padding(self, message=None, salt=None):
        """
        MD-compliant padding:
            The purpose of this padding is to ensure that the padded message is a multiple of 512 bits.
            For this padding, as a standart, message needs to have length 0<=L<2^64.
        """
        if len(message)>=(2**64):
            raise ValueError('for padding, message length needs to be less than 2**64')
        
        #convert to bits (As list/array)
        if salt is not None:
          message=salt+message
        bites=convertToBites(message)
        #print("message",message)
        #print("inbits: " , bites)
        #add 1 to it
        Length=len(bites)*8 #since our input was consisted by 8-bits bytes (string)
        bites.append(int('10000000',2))
        #add "0" for smallest, non-negative number; while L = 448 mod(512),since last 64 is for length... 
        while (len(bites)*8)%512 !=448:
            bites.append(0)
        #print("appended 0: " , bites,"\nLength",len(bites))
        #append the length of the message, in bites
        #note that: we used bin() to ease since there is no contribution of it for the understanding of the problem...
        #after converting it to bin we will know how many 0 we also need to use:
        #note that: implementations based on digest_size(32) would be more understandable in this sense, will consider.
        LenghtArray=Lengthwith64bit(Length)
        for i in LenghtArray:
            bites.append(i)
        #!! to be able to see the result of padding re-open this::
        #print('with length: ',len(bites),'\nresulting padding:',bites)
        #return bites
        return bites

    def parsing(self,message):
        """
        Parse the padded message into N 512-bit message blocks, M(1), , …, M(N) .
        where any M(n) is expressed as sixteen 32-bit words, the first 32 bits of message block i are denoted M(0(i)), the next 32 bits are M(n(i)) , and so on up to M(15(i)).
        """
        #create 512 bit objects as Matrix , which any object includes 32 bites
        width=int(512/32) #actually 16, as we previously described
        height= int((len(message)*8)/512)
        print("width:",width,"\theight:",height)
        Matrix = [[0 for x in range(width)] for y in range(height)] 
        #here we need to implement a conversion since our word length was 8 bites(bytes) in convertTobites...
        for column in range(len(Matrix)):
            for word in range(len(Matrix[column])):
              first=(column*16+word)*4
              Matrix[column][word]=wordConverter( [ message[first], message[first+1], message[first+2], message[first+3] ] )
        #parse every object into 16, 32-bit object
        #did already while convertToBites automatically
        
        #!! to be able to see the result of parsing re-open this::
        #print("resulting parsing:")
        #for i in Matrix:
        #  print(i)
        
        #return bit matrix
        return Matrix

    ###         Hash Computation           ###

    #Hashing algorithm that uses Macro Functions
    def hash(self, preprocessed):
        """
        Merkle–Damgard construction:
            Merkle Damgard construction is an hashing algorithm that builds collision resistant hash fuctions.
            Note that:
             * In some parts of the implementation here you will see ( & 0xFFFFFFFF ), this is implemented since we only want 8decimal, with overflows...
             * since digest_size -word length in bits- is 32 bits. 32bit=2^32=16^8, so we need 8 decimals in hexadecimals.
             * if there is any addition or extraction on words(aka. 32-bits digest sized...) you need to use it...
        """
        #for ease transfer the values of inital hashvalues to Array, which we also use both intermediate, and final values...
        H=self.initialHashValues.copy()
        messageBlocks=[]
        #preprocessed ( as array ) contains N many, 512-Bit structure (every particular one of them defined as "M" here). M contains 16 many 32-bit words.
        for M in range(len(preprocessed)): 
            #preparing the Message Schedule W 
            W=[0 for words in range(64)]
            for i in range(len(W)):
                if i <16:   #0 to 15
                    W[i]=preprocessed[M][i]
                else:   #15 to 63
                    W[i]=SSIG1(W[i-2]) + W[i-7] + SSIG0(W[i-15]) + W[i-16] & 0xFFFFFFFF
            
            #initialize 8 working variables , mentioned as a,b,c,d,e,f,g,h
            a=  H[ 0 ]
            b=  H[ 1 ]
            c=  H[ 2 ]
            d=  H[ 3 ]
            e=  H[ 4 ]
            f=  H[ 5 ]
            g=  H[ 6 ]
            h=  H[ 7 ]

            #Perform The Main Hash computation
            for t in range(64):
                T1 = h + BSIG1(e) + CH(e,f,g) + self._K[t] + W[t]
                T2 = BSIG0(a) + MAJ(a,b,c)
                h = g
                g = f
                f = e
                e = d + T1  & 0xFFFFFFFF
                d = c
                c = b
                b = a
                a = T1 + T2  & 0xFFFFFFFF  

                #to be able to see every iteration as a list re-open this::
                #print(M,".",t,":\t", hex(a),hex(b),hex(c),hex(d),hex(e),hex(f),hex(g),hex(h))

            #Compute the intermediate hash value H(i):
            H[ 0 ]= a + H[ 0 ] &0xFFFFFFFF  
            H[ 1 ]= b + H[ 1 ] &0xFFFFFFFF  
            H[ 2 ]= c + H[ 2 ] &0xFFFFFFFF  
            H[ 3 ]= d + H[ 3 ] &0xFFFFFFFF
            H[ 4 ]= e + H[ 4 ] &0xFFFFFFFF
            H[ 5 ]= f + H[ 5 ] &0xFFFFFFFF
            H[ 6 ]= g + H[ 6 ] &0xFFFFFFFF
            H[ 7 ]= h + H[ 7 ] &0xFFFFFFFF

            messageBlocks.append(H.copy())
        #After the above computations have been sequentially performed for all of the blocks in the message, the final output is calculated.
        #print(messageBlocks)
        lastHash=messageBlocks[len(messageBlocks)-1]
        asHex=[0 for i in range(len(lastHash))]
        #for print as hex
        for e in range(len(lastHash)):
            asHex[e]=hex(lastHash[e]) 
        return asHex
 
### tests ###
#one block
test=Sha256("abc")
for i in test.sha256:
  print(i)

#multi block
print("\t**********************************************************************************************************")
test2=Sha256("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
for i in test2.sha256:
  print(i)

#long input len=1.000.000
print("\t**********************************************************************************************************")
a=""
for i in range(1000000):
    a+="a"
test3=Sha256(a)
for i in test3.sha256:
  print(i)