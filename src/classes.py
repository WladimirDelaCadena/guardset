# TODO: in Jamie's algorithm, for adding adversary we should change the default adversary's bw 

import os
import pickle, csv, pygeoip, random
import numpy as np
from collections import namedtuple, defaultdict
import math
from binascii import hexlify
from os import urandom
import re
from collections import namedtuple, defaultdict
import copy
from sets import Set
import logging

rawdata = pygeoip.GeoIP('../requirements/GeoLiteCity.dat')
ai = pygeoip.GeoIP('../requirements/GeoIPASNum.dat')
PATH_TO__SAVE = './files'
PATH_TO__DATA = '../requirements/consensuses-2015'  # './data-2013'
PATH_AS_DATASET = '../datasets'

CREATE_THRESHOLD = 40000
MINIMUM_SETS = 50
DELETE_THRESHOLD = 20000
BREAK_SET_BW_THRESHOLD = 2*CREATE_THRESHOLD
CREATE_SUB_SET_BANDWIDTH_THRESHOLD = CREATE_THRESHOLD
PROCESSES = 4 # number of processes in multiprocesses module
DEFUALT_ADVERSARY_BW = 50
NUMBER_OF_ADVERSARIES = 1000
AFTER_DAY = '2015-01-01'
ATTACK = 2
LEAVE_THRESHOLD = 0.9
WITH_ADVERSARY = 1
ADVERSARY_TYPE = 1
NUMBER_OF_ADVERSARIES = 1
ADVERSARY_BW_FRACTION = 0.1
RANDOM_ON_DIFF_AS_NON_MEM_LIMIT_BW = 1
RANDOM_ON_DIFF_AS_NON_MEM_LIMIT_NUM = 2
RANDOM_ON_DIFF_AS_MEM_LIMIT_BW = 3
RANDOM_ON_DIFF_AS_MEM_LIMIT_NUM = 4
RANDOM_ON_SAME_AS_NON_MEM_LIMIT_BW = 5
RANDOM_ON_SAME_AS_NON_MEM_LIMIT_NUM = 6
RANDOM_ON_SAME_AS_MEM_LIMIT_BW = 7
RANDOM_ON_SAME_AS_MEM_LIMIT_NUM = 8
TOP_TIER_AS = 9
SUPERSET_ATTACKER = 10
TARGETED_ATTACK = 11
TARGETED_ATTACK_SINGLEGUARD = 13

DELIMIT = '_' # delimiter for naming the AS sets

# Type definition
Guard = namedtuple('Guard', 'name, id, bw, bw_fraction, adversary')

def adv_to_string(adv):
    # map the adversarial mode to a string
    mappie = {
        1:"The adversarial guards are located on different ASes, which are *not* in our current AS list, never-seen ASes, the adversary is bounded by BW fraction",
        2:"The adversarial guards are located on different ASes, which are *not* in our current AS list, never-seen ASes, the adversary is bounded by the number of injected guards",
        3:"The adversarial guards are located on different ASes, which *are* in our current AS list, the adversary is bounded by BW fraction",
        4:"The adversarial guards are located on different ASes, which *are* in our current AS list, the adversary is bounded by the number of injected guards",
        5:"The adversarial guards are located on the a single AS, which is *not* in our current AS list, the adversary is bounded by  BW fraction",
        6:"The adversarial guards are located on the a single AS, which is *not* in our current AS list, the adversary is bounded by  the number of injected guards",
        7:"The adversarial guards are located on the a single AS, which *is* in our current AS list, the adversary is bounded by  BW fraction",
        8:"The adversarial guards are located on the a single AS, which *is* in our current AS list, the adversary is bounded by  the number of injected guards",
        9:"The adversarial guards are located on the a single AS, which *is* top tier AS, the adversary is bounded by  BW",
        10:"The adversarial guards are located on the a single AS, which *is* top a superset, the adversary is bounded by  BW",
        11:"The adversarial guards are located on the a single AS, which *is* the targeted AS, the adversary is bounded by  BW",
        12:"Targeted attack on AS design",
        13: "Targeted attack on single guard design"
    }
    return mappie[adv]


def num_to_addr(num):
    '''
    Convert an IPv4 address from its integer representation to a string.
    @param[in] num Address as an integer.
    @returns IPv4 address as a string.
    '''
    return '%d.%d.%d.%d' % ((num >> 24) & 0xff,
                            (num >> 16) & 0xff,
                            (num >> 8) & 0xff,
                            (num & 0xff))

def gimme_asn(asn):
    try:
        s = asn.find('AS') + 2
        e = asn.find(' ')
    except:
        return None
    return asn[s:e]



def gimme_asn_database(asn_):
    #the function give a random IP from a given asn
    csv__ = open('../requirements/GeoIPASNum2.csv','r')
    csv_t = csv.reader(csv__)
    asn_database = {}
    for row in csv_t:
        asn = gimme_asn(row[2])
        if asn == asn_:
            return num_to_addr(random.randint(int(row[0]), int(row[1])))
    return None


def valid_ases():
    #the function give a the list of ASes that we have IPs for them
    csv__ = open('../requirements/GeoIPASNum2.csv','r')
    csv_t = csv.reader(csv__)
    asn_database = []
    for row in csv_t:
        asn_database.append(gimme_asn(row[2]))
    return asn_database


def ipquery(ip):
    data = rawdata.record_by_name(ip)
    if (data == None):
        return (None, None)
    return (float(data['latitude']), float(data['longitude']))


def geoquery(ip):
    data = rawdata.record_by_name(ip)
    if (data == None):
        return None
    return data['country_code']


def get_asn(ip):
    try:
        asn = ai.asn_by_addr(ip)
        if asn is not None:
            asn = asn.split(' ')
            asn = str(asn[0][2:])
            return asn
        else:
            return None
    except:
        return None

# Structure that keeps track of Guard Sets
class GuardSet(object):

    def __init__(self, guards, backup, bounds, name):
        infected = 0
        for g in guards:
            if g.adversary == 1: infected = 1

        self.guards = guards
        self.backup = backup
        self.BW_bounds = bounds
        self.infected = infected

        self.name = name


    def get_quanta(self):
        return set([(g.name, g.id) for g in self.guards])

class Relay():
    def __init__(self, id, ip, bw, coords, geo, ASN, date, ports, isExit=False, isGuard=False):
        self.ip = ip
        self.bwconsensus = int(bw)  # in bytes, from consensus
        self.isExit = isExit
        self.isGuard = isGuard
        self.code = None
        self.geocode = geo
        self.asn = ASN
        self.setnumber = None
        self.ports = ports
        self.reserved1 = ''
        self.reserved2 = ''
        self.coords = coords
        self.date = date
        self.nickname = id


class one_set():
    def __init__(self, guards):
        self.guards = guards
        self.ID = random.getrandbits(32)
        self.bw = 0

    def total_set_bandwidth(self):
        tmp = 0.0
        for g in self.guards:
            tmp += g.bwconsensus
        return tmp

    def ASes_in_set(self):
        dic = {}
        for g in self.guards:
            if g.asn not in dic: dic[g.asn] = 0
            dic[g.asn] += 1
        return len(dic.keys())

# this is contianing the state of the system.
class guard_sets():


    def __init__(self):
        self.sets = []
        self.spare = []





#-----------------------------------------------------



def parse_consensus_re(consensus, valid_ASES = None):
    # parse the network consensus files
    if valid_ASES == None: valid_ASES = Set(valid_ases())
    try:
        fi = open(consensus,'r')
        content = fi.read()
        fi.close()
        relays = {'relays' : []}
        tmp_relays = {}
        # parse out the nickname, guard flag and bandwidth
        regex2 = re.compile(r'^r\s.*\s(?P<nickname>\w*)\s.*\s(?P<ip>\d*[.]\d*[.]\d*[.]\d*)\s.*\n.*[\n]*s\s(?P<type>.*\bGuard\b.*).*\nv\s.*\nw\sBandwidth=(?P<bandwidth>[0-9]+)', re.MULTILINE)
        # Find all the matches in the consenses
        for record in regex2.finditer(content):
          # For each record, create a dictionary object for the relay
            if 'Exit' in record.group('type'): continue
            ip = str(record.group('ip'))
            asn = get_asn(ip)
            
            # we only accept asn that we have the information about them
            if asn not in valid_ASES: continue
            if asn == None: continue
            if ip is None: continue

            geo = geoquery(ip)
            coords = ipquery(ip)
            id = random.getrandbits(65)
            relay = {
                "nickname":ip,
                "ID": id,
                "bandwidth": float(record.group('bandwidth')),
                "coord": coords,
                "geo": geo,
                "asn": asn,
                "valid": None,
                "isExit": False,
                "isGuard": True,
                "ip": ip,
                "adversary": 0,
                'realID':record.group('nickname')
            }
            if ip in tmp_relays:
                tmp_relays[ip]['bandwidth'] += relay['bandwidth']
            else:
                tmp_relays[ip] = relay
          # And append it to the master list
        relays['relays']= tmp_relays.values()
        return tmp_relays
    except:
        print "Unable to open: ", consensus
        return {}



def parse_consensus(consensus_path):
    relays = []
    ip = ""
    bw = 0.0
    isExit = False
    isGuard = False

    validyear, validmonth = None, None

    try:
        f = open(consensus_path, 'r')
        for line in f:
            if validyear == None and "valid-after" in line:
                parts = line.strip().split()
                dates = parts[1].split('-')
                hour = parts[2].split(':')[0]
                validyear, validmonth, validday, validhour = int(dates[0]), int(dates[1]), int(dates[2]), int(hour)
            elif line[0:2] == "r ":
                # append the relay that we just built up


                # reset for the next relay
                bw = 0.0
                isExit = False
                isGuard = False
                ip = line.strip().split()[6]
                id = line.strip().split()[2]
                nickname = line.strip().split()[1]
            elif line[0:2] == "s ":
                if " Exit " in line: isExit = True
                if " Guard " in line: isGuard = True
            elif line[0:2] == "w ":
                bw = float(line.strip().split()[1].split("=")[1])  # KiB
                # append the relay that we just built up

            elif line[0:2] == "p ":
                p = line.strip().split("p ")[1]
                if ip != "":
                    # if ip not in list_of_ip: list_of_ip[ip] = []
                    asn = get_asn(ip)
                    geo = geoquery(ip)
                    coords = ipquery(ip)
                    valid = (validyear, validmonth, validday, validhour)
                    if isExit == False and isGuard == True:
                        rly = {
                            "nickname":id,
                            "ID": id,
                            "bandwidth": bw,
                            "coord": coords,
                            "geo": geo,
                            "asn": asn,
                            "valid": valid,
                            "isExit": isExit,
                            "isGuard": isGuard,
                            "ip": ip,
                            "adversary": 0
                        }
                        relays.append(rly)
                        # list_of_ip[ip].append(r)
            else:
                continue

        f.close()
        return relays
    except:
        print "Unable to open: ", consensus_path
        return []




def all_consensuses(ASes = None):
    consensuses = sorted(os.listdir(PATH_TO__DATA))
    if ASes == None: Set(valid_ases())
    advesary = []
    for file_name in consensuses:
        if "consensus" not in file_name:
            continue
        full_name = os.path.join(PATH_TO__DATA, file_name)
        name = re.sub('-00-00-00-consensus', '', file_name)
        current_relays =  parse_consensus_re(full_name, valid_ASES = ASes)
        yield name, current_relays



def add_adversary(relays, adv_type= ADVERSARY_TYPE, adv_num = NUMBER_OF_ADVERSARIES, adv_bw = ADVERSARY_BW_FRACTION, ASes = None):
    # this function adds the adversaies to the list of relays, The number of adversaies has been determined and they be assinged a default bandwidth.
    #this should be called after the first day
    #the adversary's relays are exit by defualt to enble us to change them to guard faster.
    # they are we be on for entire simulation
    adversary = {}
    total_bw = 0.0
    relays_bw = []
    existing_ases = []
    counter = 0
    ASes = list(ASes)
    tot_adv_bw = 0.0
    for sample in relays:
        r = relays[sample]
        total_bw += r["bandwidth"]
        relays_bw.append(r["bandwidth"])
        if r["asn"] != None: existing_ases.append(r["asn"])
    bw_frac = total_bw * float(adv_bw)
    existing_ases = list(Set(ASes) & Set(existing_ases))
    if (adv_type == RANDOM_ON_SAME_AS_MEM_LIMIT_NUM):
        sample = relays[random.choice((relays).keys())]
        asn = sample["asn"]
        for i in range(adv_num):
            name = hexlify(urandom(16))
            ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )
            adversary[ip] = rly
    #------------------------------------------------s        
    elif(adv_type == RANDOM_ON_SAME_AS_MEM_LIMIT_BW):

        sample = relays[random.choice((relays).keys())]
        asn = sample["asn"]
        tot_adv_bw = 0.0 
        while (tot_adv_bw < bw_frac):
            name = hexlify(urandom(16))
            ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )
    #------------------------------------------------              
    elif (adv_type == RANDOM_ON_SAME_AS_NON_MEM_LIMIT_NUM):
        
        assert(len(ASes) != 0), "we do not have the list of all ASes"
        excluded_ases = list(Set(ASes) - Set(existing_ases))
        asn = random.choice(excluded_ases)
        
        for i in range(adv_num):
            name = hexlify(urandom(16))
            ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )
    #------------------------------------------------         
    elif(adv_type == RANDOM_ON_SAME_AS_NON_MEM_LIMIT_BW):

        
        assert(len(ASes) != 0), "we do not have the list of all ASes"
        excluded_ases = list(Set(ASes) - Set(existing_ases))
        asn = random.choice(excluded_ases)
        
        while (tot_adv_bw < bw_frac):
            name = hexlify(urandom(16))
            ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )
    #------------------------------------------------s        
    elif(adv_type == RANDOM_ON_DIFF_AS_MEM_LIMIT_NUM):
             
        for i in range(adv_num):
            sample = relays[random.choice((relays).keys())]
            asn = sample["asn"]
            name = hexlify(urandom(16))
            ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )
    #------------------------------------------------s        
    elif(adv_type == RANDOM_ON_DIFF_AS_MEM_LIMIT_BW):
        tot_adv_bw = 0.0 
        while (tot_adv_bw < bw_frac):
            #sample = relays[random.choice((relays).keys())]
            asn = random.choice(existing_ases)
            name = hexlify(urandom(16))
            ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )
    #------------------------------------------------              
    elif (adv_type == RANDOM_ON_DIFF_AS_NON_MEM_LIMIT_NUM):
        
        assert(len(ASes) != 0), "we do not have the list of all ASes"
        excluded_ases = list(Set(ASes) - Set(existing_ases))
        
        
        for i in range(adv_num):
            asn = random.choice(excluded_ases)
            name = hexlify(urandom(16))
            ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )
    #------------------------------------------------         
    elif(adv_type == RANDOM_ON_DIFF_AS_NON_MEM_LIMIT_BW):

        assert(len(ASes) != 0), "we do not have the list of all ASes"
        excluded_ases = list(Set(ASes) - Set(existing_ases))
        tot_adv_bw = 0.0 
        while (tot_adv_bw < bw_frac):
            asn = random.choice(excluded_ases)
            name = hexlify(urandom(16))
            ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )



    elif(adv_type == TARGETED_ATTACK_SINGLEGUARD):
        assert(len(ASes) != 0), "we do not have the list of all ASes"
        excluded_ases = list(Set(ASes) - Set(existing_ases))
        tot_adv_bw = 0.0
        while (tot_adv_bw < bw_frac):
            asn = random.choice(excluded_ases)
            name = hexlify(urandom(16))
            ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )


    elif(adv_type == TOP_TIER_AS):
        tops = ['3356','174', '3257', '1299', '2914', '6453', '6762', '6939', '2828', '3549']
        #sample = relays[random.choice((relays).keys())]
        asn = random.choice(tops)
        tot_adv_bw = 0.0
        while (tot_adv_bw < bw_frac):
            name = hexlify(urandom(16))
            ip = None
            while (ip == None):
                ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )


    elif(adv_type == SUPERSET_ATTACKER):
        #sample = relays[random.choice((relays).keys())]
        #IMPORTANT this super sets are for 2015-01-01
        asn = random.choice(['6830', '44953', '44530', '4323', '4766', '577', '701', '31133', '3491', '3320', '6453', '2828', '4788', '2914', '174', '20562', '3216', '5580', '3257', '1299', '20965', '50384', '29396', '286', '7922', '209', '1239', '12989', '8359', '3356', '31025', '5511', '35395', '7029', '6939', '15412', '3561', '12389', '24785', '6461', '11537', '3549', '3223', '24724', '4637', '2516', '8928', '13030'])
        tot_adv_bw = 0.0
        while (tot_adv_bw < bw_frac):
            name = hexlify(urandom(16))
            ip = None
            while (ip == None):
                ip = gimme_asn_database(asn)
            rly = {
                "nickname":ip,
                "ID": name,
                "bandwidth": random.choice(relays_bw),
                "coord":ipquery(ip),
                "geo": geoquery(ip),
                "asn": asn,
                "valid": None,
                "isExit": True,
                "isGuard": False,
                "ip": ip,
                "adversary": 1
            }
            adversary[ip] = rly
            tot_adv_bw += rly["bandwidth"]
            counter += 1
            logging.debug("%d Adversary %s added BW:%d in IP:%s, total adv bandwidth: %d",counter,rly["asn"],int(rly["bandwidth"]),rly["ip"],int(tot_adv_bw) )



    else:
        print "ERROR: No adversary type is given!!!"  
        exit()   
    return adversary
    


    


def tmp_guard(bw):
    name = hexlify(urandom(16))
    rly = {
        "nickname":name,
        "ID": name,
        "bandwidth": bw,
        "coord":None,
        "geo": None,
        "asn": None,
        "valid": None,
        "isExit": True,
        "isGuard": False,
        "ip": None,
         "adversary": 1
    }
    return rly
