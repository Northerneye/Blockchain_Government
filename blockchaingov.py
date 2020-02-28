#this program is an proof of concept of a direct blockchain democracy, 
#there may be some insecurities in the validation protocols as I have not 
#performed intense penetration testing

#The Flask server library used needs port forwarding to be used through different networks, 
#this will work best if either two clients are set up on the same computer or two clients 
#communicate over a lan connection 

#to access the blockchain, first run this program and then go to localhost:8080, or localhost:80 if you are on the second node

#need to install Flask(Node Communication) and pycryptodome(Public-Private Keys), works on python 3.6.5

import hashlib #hashing library
import json
import time
from urllib.parse import urlparse
from uuid import uuid4
from Crypto.Signature import PKCS1_v1_5#private-public key library
from Crypto.Hash import SHA256
from Crypto.PublicKey import RSA
from base64 import b64encode, b64decode
import requests
from flask import Flask, jsonify, request, render_template  #server library, used to communicate with other nodes
import threading
import ast
import math
import os

daylength = 20 #day length in seconds, set to 20 for quick testing and demonstration
laws_per_day = 1 #number of laws that are able to be passed per day
blocksyncs = 0 #number of blocks needed to sync before voting, for larger blockchains this number will have to increase to ensure that all citizes are voting on the same laws

class Blockchain:
    def __init__(self): #initializing the blockchain
        self.current_transactions = []
        self.current_bills = []
        self.current_political_transactions = []
        self.current_votes = []
        self.chain = []
        self.nodes = []
        try: #tries to find public and private keys
            privatekey = open("govpriv.key", "r")
            self.gov_private_key = privatekey.read().encode('ISO-8859-1')
            privatekey.close()

            publickey = open("govpub.key", "r")
            self.gov_public_key = publickey.read().encode('ISO-8859-1')
            publickey.close()

            privatekey = open("coinpriv.key", "r")
            self.coin_private_key = privatekey.read().encode('ISO-8859-1')
            privatekey.close()

            publickey = open("coinpub.key", "r")
            self.coin_public_key = publickey.read().encode('ISO-8859-1')
            publickey.close()
        except: #Creates public and private keys if none are found
            govkey = RSA.generate(1024)
            self.gov_private_key = govkey.export_key()
            self.gov_public_key = govkey.publickey().export_key()
            privatekey = open("govpriv.key", 'wb+')
            privatekey.write(self.gov_private_key)
            privatekey.close()

            publickey = open("govpub.key", 'wb+')
            publickey.write(self.gov_public_key)
            publickey.close()

            coinkey = RSA.generate(1024)
            self.coin_private_key = coinkey.export_key()
            self.coin_public_key = coinkey.publickey().export_key()
            privatekey = open("coinpriv.key", 'wb+')
            privatekey.write(self.coin_private_key)
            privatekey.close()

            publickey = open("coinpub.key", 'wb+')
            publickey.write(self.coin_public_key)
            publickey.close()
        # Create the genesis block, this is where founding laws will be stored
        block = {
            'index': len(self.chain) + 1,
            'timestamp': 0,
            'transactions': [],
            'political_transactions': [{'sender': '0','recipient': self.gov_public_key.decode('ISO-8859-1'),'amount': 1000,'time': time.time(),'signature': '0'}],
            'votes': [],
            'bills': [], #founding laws are put here
            'proof': 100,
            'previous_hash': '1',
            'solved_by': ""
        }
        self.current_transactions = []
        self.current_bills = []
        self.current_political_transactions = []
        self.current_votes = []
        self.chain.append(block)
        try: #looks for a previous chain to load
            savedChain = open("blockchain.save", "r")
            self.chain = ast.literal_eval(savedChain.read())
            savedChain.close()
            print("previous blockchain loaded")
        except:
            print("chain not loaded")

    def register_node(self, address): #registers other nodes based on ip-address, has to be manually entered in this example program
        parsed_url = urlparse(address)
        if parsed_url.netloc:
            self.nodes.append(parsed_url.netloc)
            return True
        elif parsed_url.path:
            self.nodes.append(parsed_url.path)
            return True
        else:
            raise ValueError('Invalid URL')
        return False

    def valid_chain(self, chain): #checks the hashes of the previous blocks to ensure validity
        last_block = chain[0]
        current_index = 1
        while current_index < len(chain):
            block = chain[current_index]
            if block['previous_hash'] != self.hash(last_block):
                return False
            # Check that the Proof of Work is correct
            if not self.valid_proof(last_block['proof'], block['proof'], block['previous_hash']):
                return False
            last_block = block
            current_index += 1

        return True

    def resolve_conflicts(self): #gets chains from all neighbours and checks to make sure they are valid and untampered
        neighbours = self.nodes
        new_chain = None
        mined = 0
        max_length = len(self.chain)
        # Grab and verify the chains from all the nodes in our network
        for node in neighbours:
            response = requests.get(f'http://{node}/chain')
            if response.status_code == 200:
                length = response.json()['length']
                chain = response.json()['chain']
                if length > max_length and self.valid_chain(chain):
                    for x in range(len(chain)):
                        if(x>0):
                            if(chain[x]['timestamp']<chain[x-1]['timestamp']):
                                return False
                            if(int(chain[x]['index']) != int(x+1)):
                                return False
                    if(chain[len(chain)-1]['timestamp'] > time.time()):
                        return False
                    voters = []
                    index1 = 0
                    index2 = 0
                    for x in range(len(blockchain.chain)):
                        #Lets check the validity of the blockchain we are trying to adopt(does it follow all the rules?)
                        if(x != 0): #This section deals with verifying political coins donations, bills, and votes
                            if(blockchain.chain[x]['timestamp'] > blockchain.chain[x-1]['timestamp']):
                                index2 = index1+1
                                index1 = x-1
                                mybills = {}
                                for y in range(index1-index2):
                                    for vote in blockchain.chain[index2+y]['votes']:
                                        voters.append(vote['sender'])
                                for blocks in blockchain.chain:
                                    if(blocks['index'] <= index2):
                                        for bills in blocks['bills']:
                                            mybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))] = 0
                                for block in blockchain.chain:
                                    if(block['index'] <= index2):
                                        for ptransaction in block['political_transactions']:
                                            if(list(str(ptransaction['recipient']))[0] != '-'):
                                                mybills[str(ptransaction['recipient'])] = mybills[str(ptransaction['recipient'])] + int(ptransaction['amount'])
                                            if(list(str(ptransaction['recipient']))[0] == '-' and block['index'] != 1):
                                                mybills[str(ptransaction['sender'])] = mybills[str(ptransaction['sender'])] - int(ptransaction['amount'])
                                voting_laws = []
                                greatest = ''
                                for x in range(laws_per_day):
                                    greatestamount = 0
                                    for block in blockchain.chain:
                                        if(block['index'] <= index2):
                                            for bill in block['bills']:
                                                if(mybills[str(str(blockchain.hash(str(bill['bill']))+"@"+str(bill['title'])))] > greatestamount):
                                                    greatest = str(blockchain.hash(str(bill['bill']))+"@"+str(bill['title']))
                                                    greatestamount = mybills[str(str(blockchain.hash(str(bill['bill']))+"@"+str(bill['title'])))]
                                    voting_laws.append(greatest) 
                                    mybills[greatest] = 0
                                for voter in voters:
                                    existflag = False
                                    for ptransaction in blockchain.chain[x]['political_transactions']:
                                        if(ptransaction['recipient'] == voter['sender'] and ptransaction['amount'] == mybills[voter['bill']]/len(voters)):
                                            existflag = True
                                    if(existflag == False):
                                        return False
                    
                    #this section handles the cryptocurrency transactions portion of the blockchain
                    transactionnumb = 0
                    transactionnum = 0
                    nicknames = []
                    for j in range(length):
                        nicknamecheck = 0
                        for transaction in chain[j]['transactions']:
                            if (transaction['amount'] == ""):
                                return False
                            if (int(transaction['amount']) < 0):
                                return False
                            if (transaction['sender'] == transaction['recipient']):
                                return False
                            transactionnum += 1
                            if((str(transaction['sender']) != "0" or int(transaction['amount']) != 1) and (int(transaction['amount']) != 0)):
                                amount = 0
                                existflag = False
                                for blocks in chain:
                                    for ptransaction in blocks['transactions']:
                                        if(transaction['recipient'] == ptransaction['sender']):
                                            existflag = True
                                        if(str(transaction['sender']) == str(ptransaction['sender'])):
                                            if(str(transaction['signature']) == str(ptransaction['signature'])):
                                                transactionnumb += 1
                                        if (str(transaction['sender']) == str(ptransaction['sender'])):
                                            amount -= int(ptransaction['amount'])
                                        if (str(transaction['sender']) == str(ptransaction['recipient'])):
                                            amount += int(ptransaction['amount'])
                                if(existflag == False):
                                    return False
                                if(amount < 0):
                                    return False
                                importedpublickey = RSA.importKey(transaction['sender'])
                                signerpub = PKCS1_v1_5.new(importedpublickey)
                                digestpub = SHA256.new()
                                digestpub.update(bytes(str(transaction['sender'])+str(transaction['recipient'])+str(transaction['amount'])+str(transaction['time']), encoding='utf-8')) 
                                if(signerpub.verify(digestpub, transaction['signature'].encode('ISO-8859-1')) == False):
                                    return False
                            else:
                                if(int(transaction['amount']) == 0):
                                    nicknamecheck += 1
                                    nicknames.append(transaction['recipient'])
                                else:   
                                    mined += 1
                                if(j == length):
                                    if(int(transaction['amount']) == 1):
                                        if(chain[length-1]['solved_by'] != transaction['recipient']):
                                            return False
                        if(nicknamecheck > len(nicknames)):
                            return False
                    
                    for transaction in chain[j]['political_transactions']: #This section deals with verifying political coin transactions
                        if (transaction['amount'] == ""):
                            return False
                        if (int(transaction['amount']) <= 0):
                            return False
                        if (transaction['sender'] == transaction['recipient']):
                            return False
                        transactionnum += 1
                        if(list(str(transaction['sender']))[0] == "-"):
                            amount = 0
                            existflag = False
                            for blocks in chain:
                                for ptransaction in blocks['political_transactions']:
                                    if(transaction['sender'] == ptransaction['recipient']):
                                        existflag = True
                                    if(str(transaction['sender']) == str(ptransaction['sender'])):
                                        if(str(transaction['signature']) == str(ptransaction['signature'])):
                                            transactionnumb += 1
                                    if (str(transaction['sender']) == str(ptransaction['sender'])):
                                        amount -= int(ptransaction['amount'])
                                    if (str(transaction['sender']) == str(ptransaction['recipient'])):
                                        amount += int(ptransaction['amount'])
                            if(existflag == False):
                                return False
                            if(amount < 0):
                                return False
                            importedpublickey = RSA.importKey(transaction['sender'])
                            signerpub = PKCS1_v1_5.new(importedpublickey)
                            digestpub = SHA256.new()
                            digestpub.update(bytes(str(transaction['sender'])+str(transaction['recipient'])+str(transaction['amount'])+str(transaction['time']), encoding='utf-8')) 
                            if(signerpub.verify(digestpub, transaction['signature'].encode('ISO-8859-1')) == False):
                                return False
                        else:
                            if(j == length):
                                if(int(transaction['amount']) == 1):
                                    if(chain[length-1]['solved_by'] != transaction['recipient']):
                                        return False
                    for x in range(len(nicknames)):
                        for y in range(len(nicknames)):
                            if(nicknames[x] == nicknames[y] and x != y):
                                return False
                    if(transactionnum < transactionnumb):
                        return False
                    if(mined>length):
                        return False
                    max_length = length
                    new_chain = chain

        # Replace our chain if we discovered a new longer chain
        if new_chain:
            self.chain = new_chain
            for blocks in new_chain:
                for transaction in blocks['transactions']:
                    for i in range(len(self.current_transactions)):
                        if(str(self.current_transactions[i-1]['sender']) == str(transaction['sender'])):
                            if(str(self.current_transactions[i-1]['signature']) == str(transaction['signature'])):
                                del self.current_transactions[i-1]
                for ptransaction in blocks['political_transactions']:
                    for i in range(len(self.current_political_transactions)):
                        if(str(self.current_political_transactions[i-1]['sender']) == str(ptransaction['sender'])):
                            if(str(self.current_political_transactions[i-1]['signature']) == str(ptransaction['signature'])):
                                del self.current_political_transactions[i-1]
                for bill in blocks['bills']:
                    for i in range(len(self.current_bills)):
                        if(str(self.current_bills[i-1]['bill']) == str(bill['bill'])):
                            if(str(self.current_bills[i-1]['title']) == str(bill['title'])):
                                del self.current_bills[i-1]
                for vote in blocks['votes']:
                    for i in range(len(self.current_votes)):
                        if(str(self.current_votes[i-1]['sender']) == str(vote['sender'])):
                            if(str(self.current_votes[i-1]['signature']) == str(vote['signature'])):
                                del self.current_votes[i-1]
            return True
        return False

    def new_block(self, proof, previous_hash): #how to make a new block
        block = {
            'index': len(self.chain) + 1,
            'timestamp': time.time(),
            'transactions': self.current_transactions,
            'political_transactions': self.current_political_transactions,
            'votes': self.current_votes,
            'bills': self.current_bills,
            'proof': proof,
            'previous_hash': previous_hash or self.hash(self.chain[-1]),
            'solved_by': ""
        }
        self.current_transactions = []
        self.current_political_transactions = []
        self.current_votes = []
        self.current_bills = []
        self.chain.append(block)
        return block

    def new_transaction(self, sender, recipient, amount, time, signature): #how to make a new transaction
        self.current_transactions.append({
            'sender': sender,
            'recipient': recipient,
            'amount': amount,
            'time': time,
            'signature': signature
        })
        return self.last_block['index'] + 1

    def new_vote(self, sender, bill, vote, signature): #how to make a new vote
        self.current_votes.append({
            'sender': sender,
            'bill': bill,
            'vote': vote,
            'signature': signature
        })
        return self.last_block['index'] + 1

    def new_political_transaction(self, sender, recipient, amount, time, signature): #how to make a new p-transaction(mostly for bills)
        self.current_political_transactions.append({
            'sender': sender,
            'recipient': recipient,
            'amount': amount,
            'time': time,
            'signature': signature
        })
        return self.last_block['index'] + 1

    def new_bill(self, title, bill, sender, amount, time, signature): #how to make a new bill
        self.current_bills.append({
            'title': title,
            'bill': bill,
            'bill_hash': str(self.hash(str(bill)))+"@"+str(title),
            'sender': sender,
            'amount': amount,
            'time': time,
            'signature': signature
        })
        return self.last_block['index'] + 1

    def get_coin(self, address): #how to get the coin amount of any user based off their public-key/identifier
        amount = 0
        for blocks in blockchain.chain:
            for transaction in blocks['transactions']:
                if (address == transaction['sender']):
                    amount -= int(transaction['amount'])
                if (address == transaction['recipient']):
                    amount += int(transaction['amount'])
        for transactions in self.current_transactions:
            if (address == transactions['sender']):
                amount -= int(transactions['amount'])
            if (address == transactions['recipient']):
                amount += int(transactions['amount'])
        return amount

    def get_pcoin(self, address): #get the p-coin of any user based off their political public-key/identifier
        amount = 0
        for blocks in blockchain.chain:
            for transaction in blocks['political_transactions']:
                if (address == transaction['sender']):
                    amount -= int(transaction['amount'])
                if (address == transaction['recipient']):
                    amount += int(transaction['amount'])
        for transactions in self.current_political_transactions:
            if (address == transactions['sender']):
                amount -= int(transactions['amount'])
            if (address == transactions['recipient']):
                amount += int(transactions['amount'])
        for blocks in blockchain.chain:
            for transaction in blocks['bills']:
                if (address == transaction['sender']):
                    amount -= int(transaction['amount'])
        for transactions in self.current_bills:
            if (address == transactions['sender']):
                amount -= int(transactions['amount'])
        return amount

    def resolve_new_bills(self): #checks the proposed bills to make sure they are valid before adopting them into the node
        for node in self.nodes:
            response = requests.get(f'http://{node}/bill/get')
            if response.status_code == 200:
                incoming_response = response.json()[:]
                for itransaction in incoming_response:
                    myflag = True #check if they have been initialized into the blockchain or if transaction was already recieved
                    rsapubkey = RSA.importKey(itransaction['sender'].encode('ISO-8859-1')) 
                    signerpub = PKCS1_v1_5.new(rsapubkey) 
                    digestpub = SHA256.new() 
                    digestpub.update(bytes(str(itransaction['sender'])+str(str(self.hash(itransaction['bill']))+"@"+str(itransaction['title']))+str(itransaction['amount'])+str(itransaction['time']), encoding='utf-8'))
                    if(signerpub.verify(digestpub, itransaction['signature'].encode('ISO-8859-1')) == False):
                        continue
                    for blocks in blockchain.chain: #checks all blocks for a previous copy
                        for transaction in blocks['bills']:
                            if(str(transaction['bill_hash'] == itransaction['bill_hash'])):
                                if(str(transaction['title']) == str(itransaction['title'])):
                                    myflag = False
                                    break
                    for ourtransactions in self.current_bills: #checks current bills stored in node for a copy
                        if(ourtransactions['bill_hash'] == itransaction['bill_hash']):
                            if(ourtransactions['title'] == itransaction['title']):
                                myflag = False
                                break
                    if(myflag == False):
                        continue
                    if(int(itransaction['amount']) < 5): #requires a minimum amount of political currency to be a valid bill(prevents bill spamming)
                        continue
                    blockchain.current_bills.append(itransaction)#adopts bill if it is found to be valid
        return True

    def resolve_transactions(self): #checks to make sure transactions are valid before adopting them into the node
        for node in self.nodes:
            response = requests.get(f'http://{node}/transactions/get')
            if response.status_code == 200:
                incoming_response = response.json()[:]
                for itransaction in incoming_response:
                    if (itransaction['amount'] == ""):#needs an amount to be valid
                        continue
                    if (int(itransaction['amount']) < 0):# needs an amount greater than zero to be valid
                        continue
                    if (itransaction['sender'] == itransaction['recipient']):#user cannot send transactions to themselves
                        continue
                    myflag = False #check if the user has been initialized into the blockchain or if transaction was already recieved
                    for blocks in blockchain.chain:#runs through the blockchain and the transactions stored in this node to see if they have the proper funds
                        amount = 0
                        for transaction in blocks['transactions']:
                            if (str(itransaction['sender']) == str(transaction['sender'])):
                                amount -= int(transaction['amount'])
                            if (str(itransaction['sender']) == str(transaction['recipient'])):
                                amount += int(transaction['amount'])
                            for ourtransaction in self.current_transactions:
                                if (str(itransaction['sender']) == str(ourtransaction['sender'])):
                                    amount -= int(ourtransaction['amount'])
                                if (str(itransaction['sender']) == str(ourtransaction['recipient'])):
                                    amount += int(ourtransaction['amount'])
                            if(transaction['sender'] == itransaction['recipient']):
                                myflag = True
                    for ourtransaction in self.current_transactions:
                        if(ourtransaction['sender'] == itransaction['recipient']):
                            myflag = True
                    if(int(itransaction['amount']) == 0):
                        myflag = True
                    for ourtransactions in self.current_transactions:
                        if(ourtransactions['sender'] == itransaction['sender']):
                            if(ourtransactions['recipient'] == itransaction['recipient']):
                                if(ourtransactions['amount'] == itransaction['amount']):
                                    if(ourtransactions['time'] == itransaction['time']):
                                        myflag = False
                                        break
                    for blocks in blockchain.chain:#checks for a duplicate transaction
                        for transaction in blocks['transactions']:
                            if(str(transaction['sender'] == itransaction['sender'])):
                                if(str(transaction['signature']) == str(itransaction['signature'])):
                                    myflag = False
                    if(myflag == False):
                        continue
                    if (amount >= int(itransaction['amount'])):#checks if they have the proper funds, then checks if it is properly signed
                        rsapubkey = RSA.importKey(itransaction['sender'].encode('ISO-8859-1')) 
                        signerpub = PKCS1_v1_5.new(rsapubkey) 
                        digestpub = SHA256.new() 
                        digestpub.update(bytes(str(itransaction['sender'])+str(itransaction['recipient'])+str(itransaction['amount'])+str(itransaction['time']), encoding='utf-8'))
                        if(signerpub.verify(digestpub, itransaction['signature'].encode('ISO-8859-1')) == False):
                            continue
                            #throws away transaction if its not new, or not valid
                    else:
                        continue
                    blockchain.current_transactions.append(itransaction)
        return True

    def resolve_political_transactions(self): #make sure all political transactions are valid before adopting them
        for node in self.nodes:
            response = requests.get(f'http://{node}/political_transactions/get')
            if response.status_code == 200:
                incoming_response = response.json()[:]
                for itransaction in incoming_response:
                    if (itransaction['amount'] == ""):#cannot send nothing
                        continue
                    if (int(itransaction['amount']) <= 0):#have to send greater than zero currency
                        continue
                    if (itransaction['sender'] == itransaction['recipient']):
                        continue
                    myflag = False #check if they have been initialized into the blockchain or if transaction was already recieved
                    amount = 0
                    for blocks in blockchain.chain:#checks if it is a valid bill
                        for bills in blocks['bills']:
                            if(bills['bill_hash'] == itransaction['recipient']):
                                myflag = True
                    if(myflag == False):
                        continue
                    myflag = True
                    for blocks in blockchain.chain:#adds up all political funds from the blockchain
                        for transaction in blocks['political_transactions']:
                            if (str(itransaction['sender']) == str(transaction['sender'])):
                                amount -= int(transaction['amount'])
                            if (str(itransaction['sender']) == str(transaction['recipient'])):
                                amount += int(transaction['amount'])
                        for ourtransaction in self.current_political_transactions:
                            if (str(itransaction['sender']) == str(ourtransaction['sender'])):
                                amount -= int(ourtransaction['amount'])
                            if (str(itransaction['sender']) == str(ourtransaction['recipient'])):
                                amount += int(ourtransaction['amount'])
                        for bill in blocks['bills']:
                            if (str(itransaction['sender']) == str(self.hash(bill['sender']))+"@"+str(bill['title'])):
                                amount -= int(bill['amount'])
                    for ourtransactions in self.current_political_transactions:#adds all funds stored in the node
                        if(ourtransactions['sender'] == itransaction['sender']):
                            if(ourtransactions['recipient'] == itransaction['recipient']):
                                if(ourtransactions['amount'] == itransaction['amount']):
                                    if(ourtransactions['time'] == itransaction['time']):
                                        myflag = False
                                        break
                    for blocks in blockchain.chain:#checks if we already have it in the blockchain
                        for transaction in blocks['political_transactions']:
                            if(str(transaction['sender'] == itransaction['sender'])):
                                if(str(transaction['signature']) == str(itransaction['signature'])):
                                    myflag = False
                    if(myflag == False):
                        continue
                    if (amount >= int(itransaction['amount'])):#checks if they have enough currency, then checks if it is properly signed
                        rsapubkey = RSA.importKey(itransaction['sender'].encode('ISO-8859-1')) 
                        signerpub = PKCS1_v1_5.new(rsapubkey) 
                        digestpub = SHA256.new() 
                        data = bytes(str(itransaction['sender'])+str(itransaction['recipient'])+str(itransaction['amount'])+str(itransaction['time']), encoding='utf-8')
                        digestpub.update(data)
                        if(signerpub.verify(digestpub, itransaction['signature'].encode('ISO-8859-1')) == False):
                            continue
                            #take transaction off chain if invalid
                    else:
                        continue
                    blockchain.current_political_transactions.append(itransaction)
        return True

    def resolve_votes(self): #checks to make sure votes are correct before adopting them
        for node in self.nodes:
            response = requests.get(f'http://{node}/vote/get')
            if response.status_code == 200:
                incoming_response = response.json()[:]
                for itransaction in incoming_response:
                    myflag = True
                    existflag = False
                    for x in range(laws_per_day): #checks if the law is being voted on now
                        if(itransaction['bill'] == voting_laws[x]):
                            existflag = True
                    if(existflag == False):
                        return False
                    for ourtransactions in self.current_votes:#checks if we already have the vote
                        if(ourtransactions['sender'] == itransaction['sender']):
                            if(ourtransactions['bill'] == itransaction['bill']):
                                myflag = False
                                break
                    for blocks in blockchain.chain:#checks if the vote already exists in the blockchain
                        for transaction in blocks['votes']:
                            if(str(transaction['sender'] == itransaction['sender'])):
                                if(str(transaction['signature']) == str(itransaction['signature'])):
                                    myflag = False
                                    break
                        if(myflag == False):
                            break
                    if(myflag == False):
                        continue
                    #checks if signature is valid
                    rsapubkey = RSA.importKey(itransaction['sender'].encode('ISO-8859-1')) 
                    signerpub = PKCS1_v1_5.new(rsapubkey) 
                    digestpub = SHA256.new() 
                    digestpub.update(bytes(str(itransaction['sender'])+str(itransaction['bill'])+str(itransaction['vote']), encoding='utf-8'))
                    if(signerpub.verify(digestpub, itransaction['signature'].encode('ISO-8859-1')) == False):
                        continue
                        #take vote off chain if invalid
                    blockchain.current_votes.append(itransaction)
        return True

    @property
    def last_block(self):
        return self.chain[-1]

    @staticmethod
    def hash(block):
        # We must make sure that the Dictionary is Ordered, or we'll have inconsistent hashes
        block_string = json.dumps(block, sort_keys=True).encode()
        return hashlib.sha256(block_string).hexdigest()

    def proof_of_work(self, last_block):
        last_proof = last_block['proof']
        last_hash = self.hash(last_block)
        proof = 0
        while self.valid_proof(last_proof, proof, last_hash) is False:
            proof += 1

        return proof

    @staticmethod
    def valid_proof(last_proof, proof, last_hash):
        guess = f'{last_proof}{proof}{last_hash}'.encode()
        guess_hash = hashlib.sha256(guess).hexdigest()
        return guess_hash[:4] == "0000" #add zeros to make exponentially harder

#Start up flask and initialize the node
app = Flask(__name__)
 
blockchain = Blockchain()

node_identifier = blockchain.coin_public_key.decode('ISO-8859-1')

voting_laws = []

def governmentVotingManagement(): #Checks for which bills are currently being voted on
    ourindex = 0
    global voting_laws
    while(True):
        mybills = {}
        prev_block_day = math.floor(time.time()/daylength)
        for x in range(len(blockchain.chain)):
            block = blockchain.chain[len(blockchain.chain)-x-1]
            if(math.floor(block['timestamp']/daylength) < prev_block_day):
                if(x != 0):
                    ourindex = len(blockchain.chain)-x
                else:
                    ourindex = len(blockchain.chain)-x-1
                break
        if(ourindex + blocksyncs <= len(blockchain.chain)): #finds laws
            for blocks in blockchain.chain:
                if(blocks['index'] <= ourindex):
                    for bills in blocks['bills']:
                        mybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))] = 0
            for block in blockchain.chain:
                if(block['index'] <= ourindex):
                    for ptransaction in block['political_transactions']:
                        if(list(str(ptransaction['recipient']))[0] != '-'):
                            mybills[str(ptransaction['recipient'])] = mybills[str(ptransaction['recipient'])] + int(ptransaction['amount'])
                        if(list(str(ptransaction['recipient']))[0] == '-' and block['index'] != 1):
                            mybills[str(ptransaction['sender'])] = mybills[str(ptransaction['sender'])] - int(ptransaction['amount'])
                    for bill in block['bills']:
                        mybills[str(blockchain.hash(bill['bill']))+"@"+str(bill['title'])] = mybills[str(blockchain.hash(bill['bill']))+"@"+str(bill['title'])] + int(bill['amount'])
            voting_laws = []
            greatest = ''
            for x in range(laws_per_day):
                greatestamount = 0
                for block in blockchain.chain:
                    if(block['index'] <= ourindex):
                        for bill in block['bills']:
                            if(mybills[str(str(blockchain.hash(str(bill['bill']))+"@"+str(bill['title'])))] > greatestamount):
                                greatest = str(blockchain.hash(str(bill['bill']))+"@"+str(bill['title']))
                                greatestamount = mybills[str(str(blockchain.hash(str(bill['bill']))+"@"+str(bill['title'])))]
                voting_laws.append(greatest) 
                mybills[greatest] = 0
        time.sleep(5)
        
def updateBlockchain(): #Updates the blockchain and transactions and bills and votes at regular intervals
    while(True):
        try:
            blockchain.resolve_conflicts()
            blockchain.resolve_new_bills()
            blockchain.resolve_votes()
            blockchain.resolve_transactions()
            blockchain.resolve_political_transactions()
            time.sleep(5)
        except:
            time.sleep(5)

def addMainNode(): #registers a node that gives the IPs of other peers on the blockchain
    while(True):
        try:
            if(blockchain.register_node('http://127.0.0.1:80')):
                break
            time.sleep(3)
        except:
            time.sleep(3)
    print("node added")
    
def getNodes(): #gets the ips of nodes from the any connected node
    while(True):
        try:
            for node in blockchain.nodes:
                response = requests.get(f'http://{node}/nodes/get')
                if response.status_code == 200:
                    for nodes in response.json():
                        thisflag = False
                        for nodeses in blockchain.nodes:
                            if(nodeses == nodes):
                                thisflag = True
                                break
                        if(thisflag == False):
                            blockchain.nodes.append(nodes)
            time.sleep(10)
        except:
            time.sleep(10)

def saveBlockchain(): #saves the blockchain to the users computer at regular intervals
    while(True):
        try:
            privatekey = open("blockchain.save", 'wb+')
            privatekey.write(str(blockchain.chain).encode('ISO-8859-1'))
            privatekey.close()
            time.sleep(20)
        except:
            print("blockchain not saved")
            time.sleep(20)
"""
"""#comment out the one with port 80 and uncomment the one with port 8080 on the second client, then change the port to 80
try: #tries to connect to one given neighbor on the blockchain, I used two clients on the same computer while testing, one on port 80 and one on port 8080
    blockchain.register_node('http://127.0.0.1:80')
except:
    print("nodes not added")
"""
try:#for the second client
    blockchain.register_node('http://127.0.0.1:8080')
except:
    print("nodes not added")
"""
try:#tries to resolve the blockchains with any neighbors before launching
    blockchain.resolve_conflicts()
except:
    print("no neighbor chain found")
nicknameflag = False
for block in blockchain.chain: #checks if the user has a nickname and is initialized
    for transaction in block['transactions']:
        if(str(transaction['sender']) == str(node_identifier)):
            if(int(transaction['amount']) == 0):
                nicknameflag = True
if(nicknameflag == False): #lets user create nickname if they do not yet have one, nicknames help identify users rather than using public keys as their name
    nickname = input("what is your name?\n")

def initializeNode(): #if they need a nickname then this will post a nickname transaction to  the blockchain, other nodes use this transaction to find the publickey that this nickname is related to
    while(True):
        myflag = False
        for block in blockchain.chain:
            for transaction in block['transactions']:
                    if(str(transaction['sender']) == str(node_identifier)):
                        myflag = True
        for transaction in blockchain.current_transactions:
            if(str(transaction['sender']) == str(node_identifier)):
                myflag = True
        if(myflag == False):
            sender = node_identifier
            recipient = nickname
            amount = 0
            currenttime = time.time()
            data = bytes(str(sender)+str(recipient)+str(amount)+str(currenttime), encoding='utf-8')
            rsakey = RSA.importKey(blockchain.coin_private_key) 
            signer = PKCS1_v1_5.new(rsakey)
            digest = SHA256.new()
            digest.update(data)
            signature = signer.sign(digest)
            signature = signature.decode('ISO-8859-1')
            blockchain.new_transaction(sender, recipient, amount, currenttime, signature)
        time.sleep(20)

thread_list = [] #starts up the threading for side tasks and blockchain management functions
updateBlockchainThread = threading.Thread(target=updateBlockchain)
thread_list.append(updateBlockchainThread)
addMainNode = threading.Thread(target=addMainNode)
thread_list.append(addMainNode)
initializeNodeThread = threading.Thread(target=initializeNode)
thread_list.append(initializeNodeThread)
saveBlockchainThread = threading.Thread(target=saveBlockchain)
thread_list.append(saveBlockchainThread)
getOtherNodesThread = threading.Thread(target=getNodes)
thread_list.append(getOtherNodesThread)
governmentVotingManagementThread = threading.Thread(target=governmentVotingManagement)
thread_list.append(governmentVotingManagementThread)
for thread in thread_list:
    thread.start()

#from now on these are pages in flask, either for citizens to use the blockchain or for data transfer between nodes
@app.route('/', methods=['GET']) #homepage, allows user to navigate
def indexstuff():
    return render_template('homepage.html', mycoin=blockchain.get_coin(node_identifier), mypcoin=blockchain.get_pcoin(blockchain.gov_public_key.decode("ISO-8859-1")))

@app.route('/mine', methods=['GET']) #allows the user to mine the next block on website
def mine():
    #checks that all aspects of the new block is valid before attempting to add it to the chain
    voters = []
    thisindex=0
    blockchain.chain[len(blockchain.chain)-1]['solved_by'] = node_identifier
    if(math.floor(time.time()/daylength) > math.floor(blockchain.chain[len(blockchain.chain)-1]['timestamp']/daylength)):
        for x in range(len(blockchain.chain)):
            if(math.floor(blockchain.chain[len(blockchain.chain)-1-x]['timestamp']/daylength) < math.floor(blockchain.chain[len(blockchain.chain)-1]['timestamp']/daylength)):
                thisindex = len(blockchain.chain)-x
                break
        for x in range(len(blockchain.chain)-thisindex):
            for vote in blockchain.chain[thisindex+x]['votes']:
                voters.append(vote['sender'])
        mybills = {}
        for blocks in blockchain.chain:
            for bills in blocks['bills']:
                mybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))] = int(bills['amount'])
        for block in blockchain.chain:
            for ptransaction in block['political_transactions']:
                if(list(str(ptransaction['recipient']))[0] != '-'):
                    mybills[str(ptransaction['recipient'])] = mybills[str(ptransaction['recipient'])] + int(ptransaction['amount'])
        for bill in voting_laws:
            if(len(voters)>0):
                billamount = mybills[bill]/len(voters)
                for x in range(len(voters)):
                    sender = bill
                    recipient = voters[x]
                    currenttime = time.time()
                    blockchain.new_political_transaction(sender, recipient, billamount, currenttime, "0")
    for transaction in blockchain.current_transactions:#checks that all cryptocurrency transactions are valid before adding to the blockchain
        for ztransaction in blockchain.current_transactions:
            if(transaction['sender'] == ztransaction['sender'] and int(transaction['amount']) == 0 and int(ztransaction['amount']) == 0 and ztransaction['time'] != transaction['time']):
                blockchain.current_transactions.remove(transaction)
        amount = 0
        if (int(transaction['amount']) < 0):
            blockchain.current_transactions.remove(transaction)
        for blocks in blockchain.chain:
            for ptransaction in blocks['transactions']:
                if (ptransaction['sender'] == transaction['sender'] and ptransaction['signature'] == transaction['signature']):  
                    blockchain.current_transactions.remove(transaction)
                if (transaction['sender'] == ptransaction['sender']):
                    amount -= int(ptransaction['amount'])
                if (transaction['sender'] == ptransaction['recipient']):
                    amount += int(ptransaction['amount'])
        for ttransaction in blockchain.current_transactions:
            if(ttransaction['sender'] != transaction['sender'] and ttransaction['signature'] != transaction['signature']):
                if (transaction['sender'] == ttransaction['sender']):
                    amount -= int(ttransaction['amount'])
                if (transaction['sender'] == ttransaction['recipient']):
                    amount += int(ttransaction['amount'])
        if (amount < int(transaction['amount'])):
            blockchain.current_transactions.remove(transaction)
            #take invalid transaction off chain
    for transaction in blockchain.current_political_transactions:#checks that political transactions are valid
        amount = 0
        if (int(transaction['amount']) <= 0):
            blockchain.current_political_transactions.remove(transaction)
        for blocks in blockchain.chain:
            for ptransaction in blocks['political_transactions']:
                if (ptransaction['sender'] == transaction['sender'] and ptransaction['signature'] == transaction['signature']):  
                    blockchain.current_political_transactions.remove(transaction)
                if (transaction['sender'] == ptransaction['sender']):
                    amount -= int(ptransaction['amount'])
                if (transaction['sender'] == ptransaction['recipient']):
                    amount += int(ptransaction['amount'])
        for ttransaction in blockchain.current_political_transactions:
            if(ttransaction['sender'] != transaction['sender'] and ttransaction['signature'] != transaction['signature']):
                if (transaction['sender'] == ttransaction['sender']):
                    amount -= int(ttransaction['amount'])
                if (transaction['sender'] == ttransaction['recipient']):
                    amount += int(ttransaction['amount'])
        if(list(transaction['sender'])[0] != "-"):    
            for blocks in blockchain.chain:
                for bill in blocks['bills']:
                    if(str(blockchain.hash(bill['bill']))+"@"+str(bill['title']) == transaction['sender']):
                        amount += int(bill['amount'])
        if (amount < int(transaction['amount'])):
            blockchain.current_political_transactions.remove(transaction)
            #take invalid transaction off chain
    for bill in blockchain.current_bills:#checks if bills already exist
        existflag = False
        for block in blockchain.chain:
            for ibill in block['bills']:
                if(bill['title'] == ibill['title']):
                    if(bill['bill'] == ibill['bill']):
                        existflag = True
        if(existflag):
            blockchain.current_bills.remove(bill)
    #adds new block to chain after checking its validity
    last_block = blockchain.last_block
    proof = blockchain.proof_of_work(last_block)
    sender = "0"
    recipient = node_identifier
    amount = 1
    currenttime = time.time()
    data = bytes(str(sender)+str(recipient)+str(amount)+str(currenttime), encoding='utf-8')
    rsakey = RSA.importKey(blockchain.coin_private_key)
    signer = PKCS1_v1_5.new(rsakey)
    digest = SHA256.new()
    digest.update(data)
    signature = signer.sign(digest)
    signature = signature.decode('ISO-8859-1')
    blockchain.new_transaction(
        sender=sender,
        recipient=recipient,
        amount=1,
        time=currenttime,
        signature=signature
    )
    previous_hash = blockchain.hash(last_block)
    block = blockchain.new_block(proof, previous_hash)
    response = {
        'message': "New Block Forged",
        'index': block['index'],
        'transactions': block['transactions'],
        'political_transactions': block['political_transactions'],
        'votes': block['votes'],
        'bills': block['bills'],
        'proof': block['proof'],
        'previous_hash': block['previous_hash'],
    }
    return render_template('mine.html', response=response), 200

@app.route('/transactions/new', methods=['POST','GET']) #lets the user create a new cryptocurrency transaction
def new_transaction():
    if(request.method == 'POST'):
        sender = node_identifier
        recipient = ""
        for block in blockchain.chain:
            for transaction in block['transactions']:
                if(transaction['recipient'] == request.form['recipient']):
                    recipient = transaction['sender']
        if(recipient == ""):
            return "Invalid Name"
        if(recipient == sender):
            return "you cannot send money to yourself"
        amount = request.form['amount']
        if(amount == "0" or amount == ""):
            return "you have to send a greater amount than 0"
        if(int(amount) > blockchain.get_coin(node_identifier)):
            return "you do not have enough money"
        
        #signs and submits the cryptocurrency transaction
        currenttime = time.time()
        data = bytes(str(sender)+str(recipient)+str(amount)+str(currenttime), encoding='utf-8')
        rsakey = RSA.importKey(blockchain.coin_private_key)
        signer = PKCS1_v1_5.new(rsakey)
        digest = SHA256.new()
        digest.update(data)
        signature = signer.sign(digest)
        signature = signature.decode('ISO-8859-1')
        blockchain.new_transaction(sender, recipient, amount, currenttime, signature)
        return render_template('transaction.html', mycoin=blockchain.get_coin(node_identifier)), 200
    return render_template('transaction.html', mycoin=blockchain.get_coin(node_identifier)), 200

@app.route('/vote/new', methods=['POST','GET']) #lets the user see and vote on the current bills
def voting():
    bill_title = []
    bill_text = []
    for law in voting_laws:
        for block in blockchain.chain:
            for bill in block['bills']:
                if((blockchain.hash(bill['bill'])+"@"+str(bill['title'])) == law):
                    bill_title.append(bill['title'])
                    bill_text.append(bill['bill'])
    if(request.method == 'POST'):
        sender = blockchain.gov_public_key.decode("ISO-8859-1")
        bill = ""
        bill = blockchain.hash(bill_text[0])+"@"+str(bill_title[0])
        vote = -1
        if(request.form['vote'] == 'yes'):
            vote = 1
        if(request.form['vote'] == 'no'):
            vote = 0
        if(bill == ""):
            return "Invalid Bill"
        
        #signs and submits the vote
        data = bytes(str(sender)+str(bill)+str(vote), encoding='utf-8')
        rsakey = RSA.importKey(blockchain.gov_private_key)
        signer = PKCS1_v1_5.new(rsakey)
        digest = SHA256.new()
        digest.update(data)
        signature = signer.sign(digest)
        signature = signature.decode('ISO-8859-1')
        blockchain.new_vote(sender, bill, vote, signature)
        return render_template('finished_voting.html', bills_text=bill_text, bills_title=bill_title, bill_number=len(bill_title), vote=request.form['vote']), 200
    return render_template('voting.html', bills_text=bill_text, bills_title=bill_title, bill_number=len(bill_title)), 200

@app.route('/transactions/get', methods=['GET']) #used for data transfer, lets other nodes get the current transactions
def get_transaction():
    return jsonify(blockchain.current_transactions), 200

@app.route('/vote/get', methods=['GET']) #used for data transfer, lets other nodes get the current votes
def get_votes():
    return jsonify(blockchain.current_votes), 200

@app.route('/political_transactions/get', methods=['GET']) #used for data transfer, lets nodes get current political transactions
def get_political_transaction():
    return jsonify(blockchain.current_political_transactions), 200

@app.route('/bill/new', methods=['POST','GET']) #lets client propose their own bills
def new_bill():
    if(request.method == 'POST'):
        title = request.form['title']#gets the title and bill from the webpage
        bill = request.form['bill']
        amount = request.form['pCoin']
        sender = blockchain.gov_public_key.decode("ISO-8859-1")
        recipient = str(blockchain.hash(str(bill)))+"@"+str(title)
        if(amount == "0" or amount == ""):
            return "you have to send a greater amount than 0"
        if(int(amount) > blockchain.get_pcoin(sender)):
            return "you do not have enough pCoins"
        
        #signs and submits the bill
        currenttime = time.time()
        data = bytes(str(sender)+str(recipient)+str(amount)+str(currenttime), encoding='utf-8')
        rsakey = RSA.importKey(blockchain.gov_private_key)
        signer = PKCS1_v1_5.new(rsakey)
        digest = SHA256.new()
        digest.update(data)
        signature = signer.sign(digest)
        signature = signature.decode('ISO-8859-1')
        blockchain.new_bill(title, bill, sender, amount, currenttime, signature)
        return render_template('bill.html'), 200
    return render_template('bill.html'), 200

@app.route('/search_bills', methods=['POST','GET']) #searches for bills with a given keyword and presents them to the user
def search_bills():#much more complex search methods could be made, this is only a proof of concept
    if(request.method == 'POST'):
        heybills= {}
        mybills = {}
        keyword = request.form['keyword'] #gets keyword
        for blocks in blockchain.chain:
            for bills in blocks['bills']:
                if(keyword in bills['title'] or keyword in bills['bill']):
                    heybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))] = [bills['title'], bills['bill']]
                    mybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))] = 0
        for block in blockchain.chain:
            for ptransaction in block['political_transactions']:
                if(list(str(ptransaction['recipient']))[0] != '-'):
                    try:
                        mybills[str(ptransaction['recipient'])] = mybills[str(ptransaction['recipient'])] + int(ptransaction['amount'])
                    except:
                        1==1
                if(list(str(ptransaction['recipient']))[0] == '-' and block['index'] != 1):
                    try:
                        mybills[str(ptransaction['sender'])] = mybills[str(ptransaction['sender'])] - int(ptransaction['amount'])
                    except:
                        1==1
            for bill in block['bills']:
                if(keyword in bill['title'] or keyword in bill['bill']):
                    mybills[str(blockchain.hash(bill['bill']))+"@"+str(bill['title'])] = mybills[str(blockchain.hash(bill['bill']))+"@"+str(bill['title'])] + int(bill['amount'])
        modified_bill_list = []
        for blocks in blockchain.chain:
            for bills in blocks['bills']:
                if(keyword in bills['title'] or keyword in bills['bill']):
                    modified_bill_list.append([str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title'])), bills['title'], bills['bill'], mybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))]])
        return render_template('SeeBills.html', modified_bill_list=modified_bill_list, billlen=len(modified_bill_list)), 200
    return render_template('search_bills.html'), 200

@app.route('/bill', methods=['GET']) #shows all bills to the user
def show_bills():
    mybills = {}
    heybills = {}
    for blocks in blockchain.chain:#gets all bills
        for bills in blocks['bills']:
            heybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))] = [bills['title'], bills['bill']]
            mybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))] = 0
    for block in blockchain.chain:#finds the value of political currency linked to each bill
        for ptransaction in block['political_transactions']:
            if(list(str(ptransaction['recipient']))[0] != '-'):
                mybills[str(ptransaction['recipient'])] = mybills[str(ptransaction['recipient'])] + int(ptransaction['amount'])
            if(list(str(ptransaction['recipient']))[0] == '-' and block['index'] != 1):
                mybills[str(ptransaction['sender'])] = mybills[str(ptransaction['sender'])] - int(ptransaction['amount'])
        for bill in block['bills']:
            mybills[str(blockchain.hash(bill['bill']))+"@"+str(bill['title'])] = mybills[str(blockchain.hash(bill['bill']))+"@"+str(bill['title'])] + int(bill['amount'])
    modified_bill_list = []
    for blocks in blockchain.chain:
        for bills in blocks['bills']:
            modified_bill_list.append([str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title'])), bills['title'], bills['bill'], mybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))]])
    #return the bills and the political currency linked to each bill
    return render_template('SeeBills.html', modified_bill_list=modified_bill_list, billlen=len(modified_bill_list)), 200

@app.route('/political_transactions/new', methods=['POST','GET']) #lets the user donate p-coin to a bill
def new_political_transactions():
    if(request.method == 'POST'):
        sender = blockchain.gov_public_key.decode("ISO-8859-1")
        recipient = request.form['recipient']#need bill hash to donate, could be made easier for the client with a donate button integrated into the webpage but this is only a proof of concept
        existflag = False
        for block in blockchain.chain:#checks if the bill is real
            for bill in block['bills']:
                if(recipient == bill['bill_hash']):
                    existflag = True
        if(existflag == False):
            return "Invalid Bill"
        if(recipient == ""):
            return "Invalid Name"
        amount = request.form['amount']
        if(amount == "0" or amount == ""):
            return "you have to send a greater amount than 0"
        if(int(amount) > blockchain.get_pcoin(sender)):
            return "you do not have enough pCoins"
        
        #signs and submits the donation
        currenttime = time.time()
        data = bytes(str(sender)+str(recipient)+str(amount)+str(currenttime), encoding='utf-8')
        rsakey = RSA.importKey(blockchain.gov_private_key)
        signer = PKCS1_v1_5.new(rsakey)
        digest = SHA256.new()
        digest.update(data)
        signature = signer.sign(digest)
        signature = signature.decode('ISO-8859-1')
        blockchain.new_political_transaction(sender, recipient, amount, currenttime, signature)
        return render_template('political_transaction.html', mycoin=blockchain.get_pcoin(sender)), 200
    return render_template('political_transaction.html', mycoin=blockchain.get_pcoin(blockchain.gov_public_key.decode("ISO-8859-1"))), 200

@app.route('/bill/get', methods=['GET']) #used for data transfer, allows other nodes to get current bills
def get_bills():
    return jsonify(blockchain.current_bills), 200

@app.route('/chain', methods=['GET']) #used for data transfer, allows other nodes to get this user's copy of the blockchain
def full_chain():
    response = {
        'chain': blockchain.chain,
        'length': len(blockchain.chain),
    }
    return jsonify(response), 200

@app.route('/laws') #shows all passed laws to the user
def get_laws():
    ourindex = []
    global voting_laws
    mybills = {}
    prev_block_day = math.floor(time.time()/daylength)
    for x in range(len(blockchain.chain)):
        block = blockchain.chain[len(blockchain.chain)-x-1]
        if(math.floor(block['timestamp']/daylength) < prev_block_day):
            if(x != 0):
                ourindex.append(len(blockchain.chain)-x)
                prev_block_day = math.floor(blockchain.chain[len(blockchain.chain)-x]['timestamp']/daylength)
            else:
                ourindex.append(len(blockchain.chain)-x-1)
    total_voted_laws = {}
    for thisindex in ourindex:
        if(thisindex + blocksyncs <= len(blockchain.chain)): #finds laws
            for blocks in blockchain.chain:
                if(blocks['index'] <= thisindex):
                    for bills in blocks['bills']:
                        mybills[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))] = 0
            for block in blockchain.chain:
                if(block['index'] <= thisindex):
                    for ptransaction in block['political_transactions']:
                        if(list(str(ptransaction['recipient']))[0] != '-'):
                            mybills[str(ptransaction['recipient'])] = mybills[str(ptransaction['recipient'])] + int(ptransaction['amount'])
                        if(list(str(ptransaction['recipient']))[0] == '-' and block['index'] != 1):
                            mybills[str(ptransaction['sender'])] = mybills[str(ptransaction['sender'])] - int(ptransaction['amount'])
                    for bill in block['bills']:
                        mybills[str(blockchain.hash(bill['bill']))+"@"+str(bill['title'])] = mybills[str(blockchain.hash(bill['bill']))+"@"+str(bill['title'])] + int(bill['amount'])
            voting_laws = []
            greatest = ''
            for x in range(laws_per_day):
                greatestamount = 0
                for block in blockchain.chain:
                    if(block['index'] <= thisindex):
                        for bill in block['bills']:
                            if(mybills[str(str(blockchain.hash(str(bill['bill']))+"@"+str(bill['title'])))] > greatestamount):
                                greatest = str(blockchain.hash(str(bill['bill']))+"@"+str(bill['title']))
                                greatestamount = mybills[str(str(blockchain.hash(str(bill['bill']))+"@"+str(bill['title'])))]
                voting_laws.append(greatest)
                total_voted_laws[greatest] = 0 
                mybills[greatest] = 0
    for block in blockchain.chain:
        for vote in block['votes']:
            if(int(vote['vote']) == 1):
                total_voted_laws[vote['bill']] += 1
            if(int(vote['vote']) == 0):
                total_voted_laws[vote['bill']] -= 1
    passed_bills = []
    passed_laws = {}
    for bill in total_voted_laws:
        if(total_voted_laws[bill] > 0):
            passed_bills.append(bill) 
    for block in blockchain.chain:
        for bills in block['bills']:
            for bill in passed_bills:
                if(str(bill) == str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))):
                    passed_laws[str(blockchain.hash(str(bills['bill']))+"@"+str(bills['title']))] = [bills['title'], bills['bill'], bills['time']]
    return render_template('SeeLaws.html', passed_bills=passed_bills, passed_laws=passed_laws, billlen=len(passed_bills)), 200

@app.route('/nodes/get', methods=['GET']) #used for data transfer, allows other nodes to get a copy of this user's neighbor's ip-addresses
def get_otherNodes():
    thisflag = False
    for node in blockchain.nodes:
        if(node == request.remote_addr):
            thisflag = True
    if(thisflag == False):
        blockchain.nodes.append(request.remote_addr)
    return jsonify(blockchain.nodes), 200

if __name__ == '__main__':#sets up the flask server on port 8080, set up a second local computer to port 80 and follow the instructions on line 735 to connect the nodes and create a two person government!
    from argparse import ArgumentParser
    parser = ArgumentParser()
    parser.add_argument('-p', '--port', default=8080, type=int, help='port to listen on')#change to port 80 from 8080 on the second client
    args = parser.parse_args()
    port = args.port
    app.run(host='0.0.0.0', port=port, debug=False, threaded=True)
    