from __future__ import print_function
from collections import deque
import binascii
import time

# To check memory consumption:
import os
import psutil


# def convert_bytes(num):
#     """
#     this function will convert bytes to MB.... GB... etc
#     """
#     step_unit = 1000.0 #1024 bad the size

#     for x in ['bytes', 'KB', 'MB', 'GB', 'TB']:
#         if num < step_unit:
#             return "%3.1f %s" % (num, x)
#         num /= step_unit


class SimonCipher(object):
    """Simon Block Cipher Object"""

    #The constant sequence, z_x is created by a Linear Feedback Shift Register (LFSR). The logical sequence of bit constants is set by the value of the key and block sizes. The LFSR is created by a 5-bit field. The constant bit operates on a key block once per round on the lowest bit in order to add non-key-dependent entropy to the key schedule. The LFSR has different logic for each z_x sequence; however, the initial condition is the same for encryption. The initial condition of the LFSR for decryption varies on the round. z_0, z_1, z_2, z_3 and z_4 are the constant sequence. (Underscore is used to represent the subscript)

    # Z Arrays (stored bit reversed for easier usage)
    z0 = 0b01100111000011010100100010111110110011100001101010010001011111
    z1 = 0b01011010000110010011111011100010101101000011001001111101110001
    z2 = 0b11001101101001111110001000010100011001001011000000111011110101
    z3 = 0b11110000101100111001010001001000000111101001100011010111011011
    z4 = 0b11110111001001010011000011101000000100011011010110011110001011

    # valid cipher configurations stored:
    # block_size:{key_size:(number_rounds,z sequence)}
    __valid_setups = {32: {64: (32, z0)},
                      48: {72: (36, z0), 96: (36, z1)},
                      64: {96: (42, z2), 128: (44, z3)},
                      96: {96: (52, z2), 144: (54, z3)},
                      128: {128: (68, z2), 192: (69, z3), 256: (72, z4)}}

    __valid_modes = ['ECB']

    def __init__(self, key, key_size=128, block_size=128, mode='ECB', init=0, counter=0):
        """
        Initialize an instance of the Simon block cipher.
        :param key: Int representation of the encryption key
        :param key_size: Int representing the encryption key in bits
        :param block_size: Int representing the block size in bits
        :param mode: String representing which cipher block mode the object should initialize with
        :param init: IV for CTR, CBC, PCBC, CFB, and OFB modes. Here we use only Electronic Code Book
        :param counter: Initial Counter value
        :return: None
        """

        # Setup block/word size
        try:
            self.possible_setups = self.__valid_setups[block_size]
            self.block_size = block_size
            self.word_size = self.block_size >> 1
        except KeyError:
            print('Invalid block size!')
            print('Please use one of the following block sizes:', [x for x in self.__valid_setups.keys()])
            raise

        # Setup Number of Rounds, Z Sequence, and Key Size
        try:
            self.rounds, self.zseq = self.possible_setups[key_size]
            self.key_size = key_size
        except KeyError:
            print('Invalid key size for selected block size!!')
            print('Please use one of the following key sizes:', [x for x in self.possible_setups.keys()])
            raise

        # Create Properly Sized bit mask for truncating addition and left shift outputs
        self.mod_mask = (2 ** self.word_size) - 1

        # Parse the given iv and truncate it to the block length
        try:
            self.iv = init & ((2 ** self.block_size) - 1)
            self.iv_upper = self.iv >> self.word_size
            self.iv_lower = self.iv & self.mod_mask
        except (ValueError, TypeError):
            print('Invalid IV Value!')
            print('Please Provide IV as int')
            raise

        # Parse the given Counter and truncate it to the block length
        try:
            self.counter = counter & ((2 ** self.block_size) - 1)
        except (ValueError, TypeError):
            print('Invalid Counter Value!')
            print('Please Provide Counter as int')
            raise

        # Check Cipher Mode
        try:
            position = self.__valid_modes.index(mode)
            self.mode = self.__valid_modes[position]
        except ValueError:
            print('Invalid cipher mode!')
            print('Please use one of the following block cipher modes:', self.__valid_modes)
            raise

        # Parse the given key and truncate it to the key length
        try:
            self.key = key & ((2 ** self.key_size) - 1)
        except (ValueError, TypeError):
            print('Invalid Key Value!')
            print('Please Provide Key as int')
            raise

        # Pre-compile key schedule
        m = self.key_size // self.word_size
        self.key_schedule = []

        # Create list of subwords from encryption key
        k_init = [((self.key >> (self.word_size * ((m-1) - x))) & self.mod_mask) for x in range(m)]

        k_reg = deque(k_init)  # Use queue to manage key subwords

        round_constant = self.mod_mask ^ 3  # Round Constant is 0xFFFF..FC

        # Generate all round keys
        for x in range(self.rounds):

            rs_3 = ((k_reg[0] << (self.word_size - 3)) + (k_reg[0] >> 3)) & self.mod_mask

            if m == 4:
                rs_3 = rs_3 ^ k_reg[2]

            rs_1 = ((rs_3 << (self.word_size - 1)) + (rs_3 >> 1)) & self.mod_mask

            c_z = ((self.zseq >> (x % 62)) & 1) ^ round_constant

            new_k = c_z ^ rs_1 ^ rs_3 ^ k_reg[m - 1]

            self.key_schedule.append(k_reg.pop())
            k_reg.appendleft(new_k)

    def encrypt_round(self, x, y, k):
        """
        Complete One Feistel Round
        :param x: Upper bits of current plaintext
        :param y: Lower bits of current plaintext
        :param k: Round Key
        :return: Upper and Lower ciphertext segments
        """

        # Generate all circular shifts
        ls_1_x = ((x >> (self.word_size - 1)) + (x << 1)) & self.mod_mask
        ls_8_x = ((x >> (self.word_size - 8)) + (x << 8)) & self.mod_mask
        ls_2_x = ((x >> (self.word_size - 2)) + (x << 2)) & self.mod_mask

        # XOR Chain
        xor_1 = (ls_1_x & ls_8_x) ^ y
        xor_2 = xor_1 ^ ls_2_x
        new_x = k ^ xor_2

        return new_x, x

    def decrypt_round(self, x, y, k):
        """Complete One Inverse Feistel Round
        :param x: Upper bits of current ciphertext
        :param y: Lower bits of current ciphertext
        :param k: Round Key
        :return: Upper and Lower plaintext segments
        """

        # Generate all circular shifts
        ls_1_y = ((y >> (self.word_size - 1)) + (y << 1)) & self.mod_mask
        ls_8_y = ((y >> (self.word_size - 8)) + (y << 8)) & self.mod_mask
        ls_2_y = ((y >> (self.word_size - 2)) + (y << 2)) & self.mod_mask

        # Inverse XOR Chain
        xor_1 = k ^ x
        xor_2 = xor_1 ^ ls_2_y
        new_x = (ls_1_y & ls_8_y) ^ xor_2

        return y, new_x

    def encrypt(self, plaintext):
      
        try:
            b = (plaintext >> self.word_size) & self.mod_mask
            a = plaintext & self.mod_mask
        except TypeError:
            print('Invalid plaintext!')
            print('Please provide plaintext as int')
            raise


        if self.mode == 'ECB':
            b, a = self.encrypt_function(b, a)

        ciphertext = (b << self.word_size) + a

        return ciphertext


    def decrypt(self, ciphertext):
       
        try:
            b = (ciphertext >> self.word_size) & self.mod_mask
            a = ciphertext & self.mod_mask
        except TypeError:
            print('Invalid ciphertext!')
            print('Please provide ciphertext as int')
            raise

        if self.mode == 'ECB':
            a, b = self.decrypt_function(a, b)

        plaintext = (b << self.word_size) + a

        return plaintext
        

    def encrypt_function(self, upper_word, lower_word):
        
        x = upper_word
        y = lower_word 

        # Run Encryption Steps For Appropriate Number of Rounds
        for k in self.key_schedule:
             # Generate all circular shifts
            
            if (self.block_size == 64 and self.key_size == 96):
                ls_1_x = ((x >> (self.word_size - 1)) + (x << 1)) & self.mod_mask
                ls_8_x = ((x >> (self.word_size - 8)) + (x << 8)) & self.mod_mask
                ls_2_x = ((x >> (self.word_size - 2)) + (x << 2)) & self.mod_mask

                # XOR Chain
                xor_1 = (ls_1_x & ls_8_x) ^ y
                xor_2 = xor_1 ^ ls_2_x
                y = x
                x = k ^ xor_2
            else:
            
                ls_8_x = ((x >> (self.word_size - 8)) + (x << 8)) & self.mod_mask
                ls_2_x = ((x >> (self.word_size - 2)) + (x << 2)) & self.mod_mask

                # XOR Chain
                xor_1 = (x & ls_8_x) ^ y
                xor_2 = xor_1 ^ ls_2_x
                y = x
                x = k ^ xor_2
            
        return x,y    


    def decrypt_function(self, upper_word, lower_word):    
       
        x = upper_word
        y = lower_word

        # Run Encryption Steps For Appropriate Number of Rounds
        for k in reversed(self.key_schedule): 
            # Generate all circular shifts
            
            if (self.block_size == 64 and self.key_size == 96):
                ls_1_x = ((x >> (self.word_size - 1)) + (x << 1)) & self.mod_mask
                ls_8_x = ((x >> (self.word_size - 8)) + (x << 8)) & self.mod_mask
                ls_2_x = ((x >> (self.word_size - 2)) + (x << 2)) & self.mod_mask

                # XOR Chain
                xor_1 = (ls_1_x & ls_8_x) ^ y
                xor_2 = xor_1 ^ ls_2_x
                y = x
                x = k ^ xor_2
            else:
            
                ls_1_x = ((x >> (self.word_size - 1)) + (x << 1)) & self.mod_mask
                ls_8_x = ((x >> (self.word_size - 8)) + (x << 8)) & self.mod_mask
                ls_2_x = ((x >> (self.word_size - 2)) + (x << 2)) & self.mod_mask

                # XOR Chain
                xor_1 = (x & ls_8_x) ^ y
                xor_2 = xor_1 ^ ls_2_x
                y = x
                x = k ^ xor_2
            
        return x,y

#@measure_energy

def exec():
    #initialising the cipher object with encryption key
    #key = int(input("Enter Key:"))
    #key = 0x1110090801009181
    key =  0x0123456789abcdef0123456789abcdef0123456789abcdef
    #cipher = SimonCipher(key, key_size=128, block_size=128)
    #cipher = SimonCipher(key)
    cipher = SimonCipher(key,block_size = 64, key_size = 96)
    #encrypt() is the function by which the plaintext gets converted to ciphertext

    fp = open("D:/Sudhanshu/encryptioncode/textfile/128kb.txt", 'rb')

    # file_loc = 'C:\Users\chikk\Desktop\encryption code\demo.txt'
    # fp = open(file_loc,'rb')

    str1 = fp.read()
    fp.close()
    
    #print(str1)  Byte Format String
    enc_start = time.time()
    
    # pid = os.getpid()
    # py = psutil.Process(pid)
    memoryBeforeEnc = psutil.Process(os.getpid()).memory_info().rss / 1024 ** 2

    str1 = binascii.hexlify(str1).decode("utf-8")
    #print(str1)  Hex Format String
    str1 = int(str1,16)
    #print(str1)  Integer Format String
    str1 = str(str1)    #For Blocks IN STRING AGAIN
    rounds = len(str1)//16 if len(str1)//16 == len(str1)/16 else len(str1)//16 + 1
    t1 = ''
    l = []
    zero = []
    for i in range(rounds):
        #print("222",int(str1[i*16:(i+1)*16]))   Blocks of Size 128
        t = cipher.encrypt(int(str1[i*16:(i+1)*16]))
        t1 = t1 + str(t)
        l.append(len(str(t)))
        zero.append(len(str1[i*16:(i+1)*16])- len(str(int(str1[i*16:(i+1)*16]))))
        
    print("*"*10,"Encrypted Message","*"*10)
    print(t1)
    
    enc_stop = time.time()
    
    # pid = os.getpid()
    # py = psutil.Process(pid)
    memoryAfterEnc = psutil.Process(os.getpid()).memory_info().rss / 1024 ** 2
    print('memory consumption for encryption:', memoryAfterEnc - memoryBeforeEnc)
    
    print("\nEncryprtion Time (ms):",enc_stop - enc_start)
    
    #the encrypted message was displayed in hex form
    #decrypt() is the function by which the ciphertext gets converted to plaintext

    dec_start = time.time()
    
    # pid = os.getpid()
    # py = psutil.Process(pid)
    memoryBeforeDec = psutil.Process(os.getpid()).memory_info().rss / 1024 ** 2
    
    fl = ''
    sm = 0
    for i in range(rounds):    
        z = cipher.decrypt(int(t1[sm:sm+l[i]]))
        #print("111",z)
        temp = '0'*zero[i]
        fl = fl + temp + str(z)
        sm += l[i]
    #print(fl)
    #print(fl)  #Decrpted Intger Format
    fl = hex(int(fl))
    #print(fl)  #Decrpted Hex Format
    z1 = binascii.unhexlify(fl[2:])
    print("\n","*"*10,"Decrypted Message","*"*10)
    print(z1)  #Decrpted Orginal String Format
    

    #Writing to File
    fp = open('Output.txt','wb')
    fp.write(z1)
    fp.close()

    dec_stop = time.time()
    
    # pid = os.getpid()
    # py = psutil.Process(pid)
    memoryAfterDec = psutil.Process(os.getpid()).memory_info().rss / 1024 ** 2

    print('memory consumption for decryption:', memoryAfterDec - memoryBeforeDec)
    
    print("\nDecryption Time (ms):",dec_stop - dec_start)
    
 


if __name__ == "__main__":
    exec()
