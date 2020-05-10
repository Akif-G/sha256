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


class sha256:
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
    const = (0x428a2f98L, 0x71374491L, 0xb5c0fbcfL, 0xe9b5dba5L,
            0x3956c25bL, 0x59f111f1L, 0x923f82a4L, 0xab1c5ed5L,
            0xd807aa98L, 0x12835b01L, 0x243185beL, 0x550c7dc3L,
            0x72be5d74L, 0x80deb1feL, 0x9bdc06a7L, 0xc19bf174L,
            0xe49b69c1L, 0xefbe4786L, 0x0fc19dc6L, 0x240ca1ccL,
            0x2de92c6fL, 0x4a7484aaL, 0x5cb0a9dcL, 0x76f988daL,
            0x983e5152L, 0xa831c66dL, 0xb00327c8L, 0xbf597fc7L,
            0xc6e00bf3L, 0xd5a79147L, 0x06ca6351L, 0x14292967L,
            0x27b70a85L, 0x2e1b2138L, 0x4d2c6dfcL, 0x53380d13L,
            0x650a7354L, 0x766a0abbL, 0x81c2c92eL, 0x92722c85L,
            0xa2bfe8a1L, 0xa81a664bL, 0xc24b8b70L, 0xc76c51a3L,
            0xd192e819L, 0xd6990624L, 0xf40e3585L, 0x106aa070L,
            0x19a4c116L, 0x1e376c08L, 0x2748774cL, 0x34b0bcb5L,
            0x391c0cb3L, 0x4ed8aa4aL, 0x5b9cca4fL, 0x682e6ff3L,
            0x748f82eeL, 0x78a5636fL, 0x84c87814L, 0x8cc70208L,
            0x90befffaL, 0xa4506cebL, 0xbef9a3f7L, 0xc67178f2L)

    """
    For SHA-256, the initial hash value, H(0), consists of the following eight 32-bit words, in hex.  These words were obtained by taking the first thirty-two bits of the fractional parts of the square roots of the first eight prime numbers.
    primes:
        2	3	5	7	11	13	17	19
    """

    inithashvals = (0x6a09e667L, 0xbb67ae85L, 0x3c6ef372L, 0xa54ff53aL,
            0x510e527fL, 0x9b05688cL, 0x1f83d9abL, 0x5be0cd19L)

    
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
            return (x>>n) | (x<<(digest_size-n)) &
        except:
            raise ValueError 'n should be less than 32 in sha256 for RotateRight %s()'%(n)
    
    def SHR(n,x):
        # SHR^n(x) = x>>n
        # The right shift operation SHR^n(x), where x is a w-bit (digest_size) word and n is an integer with 0 <= n < w.
        try:
            return (x>>n)
        except:
            raise ValueError 'n should be less than 32 in sha256 for RotateRight %s()'%(n)

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

    def __init__(self, message=None, salt=None):
        if message is not None:
            if type(message) is not str:
                raise TypeError, '%s() argument 1 must be string, not %s' % (self.__class__.__name__, type(message).__name__)

        # Timeline of the processes:
        padded=padding(message,salt)
        parsed=parsing(padded)
        self.sha256=sha256(parsed)


    def padding(self, message=None, salt=None):
        """
        The purpose of this padding is to ensure that the padded message is a multiple of 512 bits.
        For this padding, as a standart, message needs to have length L<2^64.
        """
        if len(message)>=(2**64):
            raise ValueError,'for padding message\'s length needs to have less than 2^64'
        
        #convert to bits
        
        #add 1 to it

        #add "0" for smallest, non-negative times; while L = 448 mod(512),since last 64 is for length... 
        
        #append the length of the message, in bites
    
        #return bites

    def parsing(self,message):
        """
        Parse the padded message into N 512-bit message blocks, M(1), , …, M(N) .
        where any M(n) is expressed as sixteen 32-bit words, the first 32 bits of message block i are denoted M(0(i)), the next 32 bits are M(n(i)) , and so on up to M(15(i)).
        """
        #create 512 bit objects

        #parse every object into 16, 32-bit object

        #return bit matrix

    def hash(self, parsed):
        #will be processed...
        