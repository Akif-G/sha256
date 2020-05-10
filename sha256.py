"""
* Filename:   sha256.py
* Author:     Akif-G (mehmetgultekin  At  sabanciuniv.edu)
* Copyright:
* Disclaimer: This code is presented "as is" without any guarantees.
* Details:    Implementation of the SHA-256 hashing algorithm.
              SHA-256 is one of the three algorithms in the SHA2
              specification. The others, SHA-384 and SHA-512, are not
              offered in this implementation.
              Algorithm specification can be found here:
               * http://csrc.nist.gov/publications/fips/fips180-2/fips180-2withchangenotice.pdf     
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
    collided=0
    for elem in arrayOfElems:
        collided=collided*(2**8)+elem
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
    #collide into 8 bites:
    asBin=""
    asHex=[]
    for j in range(64):
        if (j+1)%8!=0:
            asBin+=str(arr[i])
        else:
            asBin+=str(arr[i])
            asHex.append(asBin)
            asBin=""
    #convert from binary to integer -8 bit...
    asDec=[]
    for string in asHex:
        asDec.append(int(string,2))
    return asDec







class Sha256:

    def __init__(self, message, salt=None):
        if message is not None:
            if type(message) is not str:
                raise TypeError('%s() argument 1 must be string, not %s' % (self.__class__.__name__, type(message).__name__))

        # Timeline of the processes:
        padded=self.padding(message,salt)
        parsed=self.parsing(padded)
        self.sha256=self.hash(parsed)


    def padding(self, message=None, salt=None):
        """
        The purpose of this padding is to ensure that the padded message is a multiple of 512 bits.
        For this padding, as a standart, message needs to have length 0<=L<2^64.
        """
        if len(message)>=(2**64):
            raise ValueError('for padding, message length needs to be less than 2**64')
        
        #convert to bits (As list/array)
        if salt is not None:
            message=salt+message
        bites=convertToBites(message)
    
        #add 1 to it
        bites.append(int('10000000',2))
        Length=len(bites)-1
        #add "0" for smallest, non-negative number; while L = 448 mod(512),since last 64 is for length... 
        while (len(bites)*8)%512 !=448:
            bites.append(0)
        #append the length of the message, in bites
        #note that: we used bin() to ease since there is no contribution of it for the understanding of the problem...
        #after converting it to bin we will know how many 0 we also need to use:
        #note that: implementations based on digest_size(32) would be more understandable in this sense, will consider.
        LenghtArray=Lengthwith64bit(Length)
        for i in LenghtArray:
            bites.append(i)
        #return bites
        return bites

    def parsing(self,message):
        """
        Parse the padded message into N 512-bit message blocks, M(1), , …, M(N) .
        where any M(n) is expressed as sixteen 32-bit words, the first 32 bits of message block i are denoted M(0(i)), the next 32 bits are M(n(i)) , and so on up to M(15(i)).
        """
        #create 512 bit objects as Matrix , which any object includes 32 bites
        width=int(512/32)
        heigth= int(len(message)/512)
        Matrix = [[0 for x in range(width)] for y in range(heigth)] 
        #here we need to implement a conversion since our word length was 8 bites(bytes) in convertTobites...
        for column in range(len(Matrix)):
            for word in range(len(Matrix[column])):
                first=(column*16+word)*4
                Matrix[column][word]=wordConverter( [ message[first], message[first+1], message[first+2], message[first+3] ] )
        #parse every object into 16, 32-bit object
        #did already while convertToBites automatically

        #return bit matrix
        return Matrix

    def hash(self, processed):
        print(processed)
        #will be processed...
    
        """
    algorithm can be defined in two stages:
        preprocessing:
            Preprocessing involves padding a message, parsing the padded message into m-bit blocks, and setting initialization values to be used in the hash computation. 
        
        hash computation:
            The hash computation generates a message schedule from the padded message and uses that schedule, along with functions, constants, and word operations to iteratively generate a series of hash values.
    """


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
    consts = (0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
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
                0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2)

    """
    For SHA-256, the initial hash value, H(0), consists of the following eight 32-bit words, in hex.  These words were obtained by taking the first thirty-two bits of the fractional parts of the square roots of the first eight prime numbers.
    primes:
        2	3	5	7	11	13	17	19
    """

    inithashvals = (0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
            0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19)

    
    ####

    ##MACRO FUNCTIONS
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
            return (x>>n) | (x<<(32-n)) #32=digest_size can be implemented as an input vice versa
        except:
            raise ValueError( 'n should be less than 32 in sha256 for RotateRight %s()'%(n))
    
    def SHR(n,x):
        # SHR^n(x) = x>>n
        # The right shift operation SHR^n(x), where x is a w-bit (digest_size) word and n is an integer with 0 <= n < w.
        try:
            return (x>>n)
        except:
            raise ValueError('n should be less than 32 in sha256 for RotateRight %s()'%(n))

    def EP0(n,x):
        # BSIG0(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x)
        return ROTR(2,x) ^ROTR(13,x)^ROTR(22,x)

    def EP1(n,x):
        # BSIG0(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x)
        return ROTR(6,x) ^ROTR(11,x)^ROTR(25,x)
    
    def SIG0(n,x):
        # SSIG0(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x)
        return ROTR(7,x) ^ROTR(18,x)^SHR(3,x)
    
    def SIG1(n,x):
        # SSIG1(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x)
        return ROTR(17,x) ^ROTR(19,x)^SHR(10,x)

    ####

        
print(type('mamar'))
Sha256(message='mamar')