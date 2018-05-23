#!/usr/bin/env python
# !/usr/bin/env python


'''
 ###################################  My Notes: ###################################
In subsets:
ssets.adversary = the number of adversary guards
sset.adv_bandwidth = total bandwidth of adversary guards

In sets:
set.adversary  = the number of adversary subsets
set.adv_bandwidth = total bandwidth of adversary subsets

I users:
user.adversary = ssets.adversary
user.adv_bandwidth = sset.adv_adv_bandwidth

 ###################################  My Notes: ###################################

'''
import re, os, random, pickle, argparse, time, algorithm
from  collections import namedtuple, defaultdict, Counter
from sets import Set, ImmutableSet
import networkx as nx
import classes
import numpy, math
import copy
import logging
import multiprocessing
from multiprocessing import Lock, Process, Queue, current_process, Pool,Value
from binascii import hexlify
from os import urandom
logging.basicConfig(filename='logs.log', filemode='w', format='%(levelname)s:%(message)s', level=logging.CRITICAL)

as_info = namedtuple('as_info', 'asn, providers, customers, peers, siblings')
##############################################################
##############################################################
#################NOTE NOTE NOTE NOTE NOTE#####################
##############################################################
##############################################################
# All the ASNs are string not int






# -----------------------------------
# some constant values that we need them in the code
PROVIDER_TO_CUSTOMER = 1
CUSTOMER_TO_PROVIDER = 2
SIBLING_TO_SIBLING = 3
PEER_TO_PEER = 4

# states
UPDATING = 1
UPDATED = 2
REGROUPING = 3
REGROUPED = 4

# guard selection methods
TOR = 1
AS_BASED = 2
JAMIE = 3


# ----------------------------------

class MyCounter(object):
    def __init__(self, initval=0):
        self.val = Value('i', initval)
        self.lock = Lock()

    def increment(self):
        with self.lock:
            self.val.value += 1

    def value(self):
        with self.lock:
            return self.val.value


def unwrap_self_f(arg, **kwarg):
    return as_set_proccess.f(*arg, **kwarg)


def set_user(x=None):
    user = [str(random.randint(1, 999999999999)), None, 0]
    '''
    user = {
            'guard_bandwidth': 0.0,
            'id': None,
            'guard': None,
            'guard_asn': None,
            'pre_guards': Set([]),
            'pre_ases': Set([]),
            'adversary': 0,
            'adv_bandwidth' : 0.0,
            'subset_id' : None,
            'set_id' : None
    }
    user['id'] = str(random.randint(1, 999999999999))
    '''
    return user


class Quanta():
    def __init__(self):
        self.id = None
        self.guards = []
        self.active_ases = Set([])  # ases that carry guards not the providers
        self.adversary = 0.0  # the number of adversaries guards in the sset
        self.bandwidth = 0.0  # the list of guards bandwidth in sset


class autonomous_system():
    def __init__(self):
        self.asn = None
        self.peers = Set([])
        self.cone = Set([])
        self.hierarchy_providers = Set([])
        self.siblings = Set([])
        self.siblings_chain = Set([])


class Subset():
    def __init__(self):
        self.bandwidth = 0.0
        self.ases = Set([])
        self.id = None
        self.guards = []
        self.size = 0
        self.died_guards = []
        self.died_ases = Set([])
        self.active_ases = Set([])  # ases that carry guards not the providers
        self.adversary = 0  # the number of adversaries guards in the sset
        self.adv_bandwidth = 0.0  # the bandwidth of adversarial guards in sset
        self.bandwidth_list = []  # the list of guards bandwidth in sset
        self.provider = None
        self.quantum = []

    def copy_subset(self, copyee):
        # copy a sset in another one
        self.bandwidth = copyee.bandwidth
        self.ases |= copyee.ases
        self.id = copyee.id
        self.guards.extend(copyee.guards)
        self.size = copyee.size
        self.died_guards.extend(copyee.died_guards)
        self.died_ases |= copyee.ases
        self.active_ases |= copyee.active_ases  # ases that carry guards not the providers
        self.adversary = copyee.adversary
        self.adv_bandwidth = copyee.adv_bandwidth
        self.bandwidth_list.extend(copyee.bandwidth_list)
        self.provider = copyee.provider
        self.quantum = copy.copy(copyee.quantum)

    def give_sset_id(self):
        if self.id == None: return None
        return (self.id).split(classes.DELIMIT)[1]


class UserClass():
    def __init__(self):
        self.guard_bandwidth = 0.0
        self.id = None
        self.guard = None
        self.guard_asn = None
        self.pre_guards = Set([])
        self.pre_ases = Set([])
        self.adversary = 0  # the number of adversarial guards in the user's sset
        self.adv_bandwidth = 0.0  # total bandwidth of adversarial guards in sset
        self.subset_id = None  # ASN_ID_i_Q
        self.set_id = None  # ASN


class as_set():
    def __init__(self):
        self.bandwidth = 0.0
        self.ases = Set([])
        self.id = None
        self.guards = []
        self.size = 0
        self.died_guards = []
        self.died_ases = Set([])
        self.active_ases = Set([])  # ases that carry guards not the providers
        self.subsets = []
        self.adversary = 0  # the number adversarial sset in the set
        self.adv_bandwidth = 0.0
        self.assigned_users = 0  # the number of users assigned to this set
        self.utilized = 0.0  # (set's bw/ total bw) - (assigned users/total users)


class as_set_proccess():
    def __init__(self):
        self.original = {}  # original ASes in each day, before any set or grouping
        self.as_list = {}
        self.providers = {}
        self.customers = {}
        self.links = {}
        self.all_ases = {}
        self.PATH_TO_DATASET = classes.PATH_AS_DATASET
        self.AS_RELATIONSHIPS = '20150701.as-rel.txt'
        self.today_sets = {}
        self.yesterday_sets = {}
        self.date = ''
        self.first_day_sets = {}
        self.never_seen_ases = Set([])  # never been seen ASes
        self.state = 0
        self.tmp_sets = {}
        self.today_bw = 0.0
        self.relays = {}
        self.selection = AS_BASED
        self.number_of_users = 1000000
        self.today_alive_sets = []
        self.map_as_set = {}
        self.quantum_numbers = 0
        self.compromise_rate = 0.0  # fraction of users with adversarial sset to total number of users
        self.utilized = 0.0
        self.MINIMUM_SETS = 50  # minimum number of sets that we should have
        self.ADVERSARY_TYPE = 1  # the type of adversary we would like to have
        self.CREATE_THRESHOLD = 40000  # minimum bw allowed for creation of sets
        self.DELETE_THRESHOLD = 20000  # minimum bw allowed for deletion of sets
        self.our_adversaries = {}  # our added adversaries after day one
        self.adv_bw_fraction = 0.0  # the adversary fraction in the network
        self.adv_num = 0  # the number of adversaries we need to add to the network
        self.users_queue = Queue()  # the queue we save the users
        self.compromised_users = Set([])
        self.today_quantum = Set([])
        self.yesterday_quantum = Set([])
        self.killed_ssets = 0
        self.created_ssets = 0
        self.today_all = []
        self.sset_to_quanta = {}
        self.quanta_to_sset = {}
        self.set_to_quanta = {}
        self.jamies_users_compromised = set()
        self.jamies_users_compromised_rate = 0.0
        self.single_guard_users_compromised = Set([])
        self.single_guard_users_compromised_rate = 0.0
        self.jamies_median_bw = 0.0
        self.single_guard_median_bw = 0.0
        self.number_jamies_sets = 0
        self.relays_bws = []
        self.CREATE_THRESHOLD_SSET = self.CREATE_THRESHOLD
        self.user_change_quanta = 0
        self.user_change_sset = 0
        self.user_change_set = 0
        self.AFTER_DAY = '2015-01-01'
        self.adversarial_ASes = Set([])
        self.adversarial_bw = -1.0
        self.interations = 0
	self.multipath = 0 #Wladimir

    def reset(self):
        self.original = {}  # original ASes in each day, before any set or grouping
        self.as_list = {}
        self.today_sets = {}
        self.yesterday_sets = {}
        self.date = ''
        self.first_day_sets = {}
        self.never_seen_ases = Set([])  # never been seen ASes
        self.state = 0
        self.tmp_sets = {}
        self.today_bw = 0.0
        self.relays = {}
        self.selection = AS_BASED
        self.today_alive_sets = []
        self.map_as_set = {}
        self.quantum_numbers = 0
        self.compromise_rate = 0.0  # fraction of users with adversarial sset to total number of users
        self.utilized = 0.0
        self.DELETE_THRESHOLD = 20000  # minimum bw allowed for deletion of sets
        self.our_adversaries = {}  # our added adversaries after day one
        self.users_queue = Queue()  # the queue we save the users
        self.compromised_users = Set([])
        self.today_quantum = Set([])
        self.yesterday_quantum = Set([])
        self.killed_ssets = 0
        self.created_ssets = 0
        self.today_all = []
        self.sset_to_quanta = {}
        self.quanta_to_sset = {}
        self.set_to_quanta = {}


    def final_update(self):
        # go through the sets and update the bandwidth and adversary flag
        # TODO: adversary's bw is not divided by the quanta, they are whole, also bandwidth_list includes the pure bandwidth, not divided by quanta.

        bandwidth_check = 0.0
        for set_ in self.today_sets:
            tot_bw_set = 0.0
            for act in self.today_sets[set_].active_ases:
                tot_bw_set += self.original[act].bandwidth
            tmp_set_as = Set([])
            for sub in self.today_sets[set_].subsets:
                tmp_adv_bw_sub = 0.0
                adv_sub = 0
                tmp_set_as |= sub.active_ases
                tot_bw_sub = 0.0
                bandwidth = []
                # alive_sets.append(sub.id)
                for g in sub.guards:
                    tot_bw_sub += self.relays[g]["bandwidth"]
                    bandwidth.append(self.relays[g]["bandwidth"])
                    adv_sub += self.relays[g]["adversary"]
                    if self.relays[g]["adversary"] != 0:
                        logging.debug("We have an adversary in %s sset with bandwidth %d and set %s with bandwidth %d",
                                     sub.id, int(sub.bandwidth), set_, int(self.today_sets[set_].bandwidth))
                    if (self.relays[g]["adversary"] == 1):
                        tmp_adv_bw_sub += self.relays[g]["bandwidth"]
                sub.adversary = adv_sub
                sub.adv_bandwidth = tmp_adv_bw_sub
                sub.bandwidth_list = copy.copy(bandwidth)

                bw_quantum = 0.0
                quanta_adv = 0.0
                tmp_active_ases = Set([])
                all_guards = []
                subid = sub.id.split(classes.DELIMIT)[1]
                # self.sset_to_quanta[subid] = []
                for q in sub.quantum:
                    # logging.debug("Quanta:id:%s\tbw:%d\tguards:%d\tAS:%s",q.id,int(q.bandwidth), len(q.guards),q.active_ases)
                    tmp_active_ases |= q.active_ases
                    tmp_q_bw = 0.0
                    all_guards.extend(q.guards)
                    quanta_adv = 0.0
                    for g in q.guards:
                        tmp_q_bw += self.relays[g]["bandwidth"]
                        if self.relays[g]["adversary"] != 0:
                            logging.debug(
                                "We have an adversary in quanta %s with bandwidth %d and set %s with bandwidth %d",
                                q.id, int(q.bandwidth), set_, int(self.today_sets[set_].bandwidth))
                            quanta_adv += 1
                    assert (sub.id in q.id), "{0} == {1}".format(sub.id, q.id)
                    assert (q.bandwidth == tmp_q_bw), "{0} == {1}".format(q.bandwidth, tmp_q_bw)
                    bw_quantum += q.bandwidth
                    q.adversary = quanta_adv
                    # self.today_quantum |= Set([self.get_quanta_id(q.id)])
                    bandwidth_check += q.bandwidth
                    # self.today_all.append((q.id, q.bandwidth, q.adversary))
                    # self.sset_to_quanta[subid].append((q.id, q.bandwidth, q.adversary,sub.bandwidth))
                    # self.set_to_quanta[set_].append((q.id, q.bandwidth, q.adversary,sub.bandwidth))
                    # self.quanta_to_sset[self.get_quanta_id(q.id)] = (sub.id,q.id,q.bandwidth,q.adversary)
                    # self.all_quantum[q.id] = copy.copy(q.guards)
                    # assert (len(self.all_quantum[q.id]) != 0), '{0} {1}'.format(q.id,self.all_quantum[q.id])

                assert (len(all_guards) == len(sub.guards)), "{0} == {1}".format(len(all_guards), len(sub.guards))
                assert (tot_bw_sub == sub.bandwidth), "{0} == {1}".format(tot_bw_sub, sub.bandwidth)
                assert (bw_quantum == sub.bandwidth), "{0} == {1}".format(bw_quantum, sub.bandwidth)

            tmp_adv_bw_set = 0.0
            adv = 0
            for sub in self.today_sets[set_].subsets:
                adv += sub.adversary
                tmp_adv_bw_set += sub.adv_bandwidth
            self.today_sets[set_].adversary = adv
            self.today_sets[set_].adv_bandwidth = tmp_adv_bw_set
            assert (abs(tot_bw_set - self.today_sets[set_].bandwidth) < 10), "The set does not have correct bandwidth"
            assert (len(self.today_sets[set_].active_ases - tmp_set_as) == 0), "The set is not correct"
        assert (bandwidth_check == self.today_bw), "{0} == {1}".format(bandwidth_check, self.today_bw)
        # self.today_alive_sets = copy.copy(alive_sets)
        # self.map_as_set = copy.copy(as_in_set)
        # self.quantum_numbers = sets_num




        # -------------------------------------------------------
        if False: #skip this part for now
            died_sets = []
            for set_ in self.today_sets:
                if self.today_sets[set_].bandwidth == 0 or len(self.today_sets[set_].active_ases) == 0:
                    died_sets.append(set_)
            for set_ in died_sets:
                del self.today_sets[set_]
                logging.info("we killed set %s ", set_)

            for set_ in self.today_sets:
                died_ssets = []
                for sub in self.today_sets[set_].subsets:
                    if sub.bandwidth == 0 or len(sub.active_ases) == 0:
                        died_ssets.append(sub)
                for sset in died_ssets:
                    self.today_sets[set_].remove(sset)
                    logging.info("we killed sset %s ", sset.id)

                for sub in self.today_sets[set_].subsets:
                    died_quantum = []
                    for q in sub.quantum:
                        if q.bandwidth == 0 or len(q.active_ases) == 0:
                            died_quantum.append(q)
                    for q in died_quantum:
                        sub.quantum.remove(q)
                        logging.info("we killed quanta %s ", q.id)


        # ---------------------------------------------------------



        alive_sets = []
        as_in_set = {}
        sets_num = 0
        self.today_quantum = Set([])
        self.today_all = []
        self.sset_to_quanta = {}
        self.quanta_to_sset = {}
        self.set_to_quanta = {}
        bandwidth_check = 0.0
        for set_ in self.today_sets:
            self.set_to_quanta[set_] = []
            self.today_sets[set_].assigned_users = 0
            tot_bw_set = 0.0
            for act in self.today_sets[set_].active_ases:
                as_in_set[act] = set_
                tot_bw_set += self.original[act].bandwidth
            tmp_set_as = Set([])
            for sub in self.today_sets[set_].subsets:
                tmp_adv_bw_sub = 0.0
                adv_sub = 0
                tmp_set_as |= sub.active_ases
                tot_bw_sub = 0.0
                bandwidth = []
                # alive_sets.append(sub.id)
                for g in sub.guards:
                    tot_bw_sub += self.relays[g]["bandwidth"]
                    bandwidth.append(self.relays[g]["bandwidth"])
                    adv_sub += self.relays[g]["adversary"]
                    if self.relays[g]["adversary"] != 0:
                        logging.debug("We have an adversary in %s sset with bandwidth %d and set %s with bandwidth %d",
                                     sub.id, int(sub.bandwidth), set_, int(self.today_sets[set_].bandwidth))
                    if (self.relays[g]["adversary"] == 1):
                        tmp_adv_bw_sub += self.relays[g]["bandwidth"]
                sub.adversary = adv_sub
                sub.adv_bandwidth = tmp_adv_bw_sub
                sub.bandwidth_list = copy.copy(bandwidth)

                bw_quantum = 0.0
                quanta_adv = 0.0
                tmp_active_ases = Set([])
                all_guards = []
                subid = sub.id.split(classes.DELIMIT)[1]
                self.sset_to_quanta[subid] = []
                for q in sub.quantum:
                    # logging.debug("Quanta:id:%s\tbw:%d\tguards:%d\tAS:%s",q.id,int(q.bandwidth), len(q.guards),q.active_ases)
                    sets_num += 1
                    tmp_active_ases |= q.active_ases
                    tmp_q_bw = 0.0
                    #logging.info("BW-EVAL:%s:\t:%s -- %d", self.date,q.id, int(q.bandwidth))
                    all_guards.extend(q.guards)
                    quanta_adv = 0.0
                    for g in q.guards:
                        logging.debug("QID:%s---> Guard: %s", q.id, g)
                        tmp_q_bw += self.relays[g]["bandwidth"]
                        if self.relays[g]["adversary"] != 0:
                            logging.debug(
                                "We have an adversary in quanta %s with bandwidth %d and set %s with bandwidth %d",
                                q.id, int(q.bandwidth), set_, int(self.today_sets[set_].bandwidth))
                            quanta_adv += 1
                    assert (sub.id in q.id), "{0} == {1}".format(sub.id, q.id)
                    assert (q.bandwidth == tmp_q_bw), "{0} == {1}".format(q.bandwidth, tmp_q_bw)
                    bw_quantum += q.bandwidth
                    q.adversary = quanta_adv
                    self.today_quantum |= Set([self.get_quanta_id(q.id)])
                    bandwidth_check += q.bandwidth
                    self.today_all.append((q.id, q.bandwidth, q.adversary))
                    self.sset_to_quanta[subid].append((q.id, q.bandwidth, q.adversary, sub.bandwidth))
                    self.set_to_quanta[set_].append((q.id, q.bandwidth, q.adversary, sub.bandwidth))
                    self.quanta_to_sset[self.get_quanta_id(q.id)] = (sub.id, q.id, q.bandwidth, q.adversary)
                    # self.all_quantum[q.id] = copy.copy(q.guards)
                    # assert (len(self.all_quantum[q.id]) != 0), '{0} {1}'.format(q.id,self.all_quantum[q.id])

                assert (len(all_guards) == len(sub.guards)), "{0} == {1}".format(len(all_guards), len(sub.guards))
                assert (tot_bw_sub == sub.bandwidth), "{0} == {1}".format(tot_bw_sub, sub.bandwidth)
                assert (bw_quantum == sub.bandwidth), "{0} == {1}".format(bw_quantum, sub.bandwidth)

            tmp_adv_bw_set = 0.0
            adv = 0
            for sub in self.today_sets[set_].subsets:
                adv += sub.adversary
                tmp_adv_bw_set += sub.adv_bandwidth
            self.today_sets[set_].adversary = adv
            self.today_sets[set_].adv_bandwidth = tmp_adv_bw_set
            assert (abs(tot_bw_set - self.today_sets[set_].bandwidth) < 10), "The set does not have correct bandwidth"
            assert (len(self.today_sets[set_].active_ases - tmp_set_as) == 0), "The set is not correct"
        assert (bandwidth_check == self.today_bw), "{0} == {1}".format(bandwidth_check, self.today_bw)
        self.today_alive_sets = copy.copy(alive_sets)
        self.map_as_set = copy.copy(as_in_set)
        self.quantum_numbers = sets_num
        logging.debug("we have %d subsets today (total %d), %d new subsets", len(self.today_quantum),
                     self.quantum_numbers,
                     len(self.today_quantum & self.yesterday_quantum))
        logging.debug("we have %d sets today , %d new sets", len(self.today_sets),
                     len(Set(self.today_sets.keys()) & Set(self.yesterday_sets.keys())))

        # logging.debug("today: %s", self.today_subsets)
        # logging.debug("New: %s", self.today_subsets & self.yesterday_subsets)

        #print information about the guard set
        for set_ in self.today_sets:
            for sub in self.today_sets[set_].subsets:
                for q in sub.quantum:
                    for g in q.guards:
                        logging.info("ASDAY:%s:SuS:%s:SeS:%s:QU:%s:IP:%s:AS:%s:BW:%d:P:%s",self.date,set_,sub.id,q.id,g,self.relays[g]["asn"],int(self.relays[g]["bandwidth"]),sub.provider)

        for g in self.relays:
            logging.info("SGDAY:%s:IP:%s:AS:%s:BW:%d",self.date,g,
                             self.relays[g]["asn"], int(self.relays[g]["bandwidth"]))









    def parse_as_relationships(self):
        ##############################################################
        ##############################################################
        #################Parse the AS relationships###################
        ##############################################################
        ##############################################################
        fil = open(self.PATH_TO_AS_RELATIONSHIPS, 'r')  # 'oix_relation_degree'
        rd = fil.read()
        p = re.compile(
            r"AS(?P<asn>\d*):?\nProviders:#[0-9]*::(?P<providers>.*)\nCustomers:#[0-9]*::(?P<customers>.*)\nPeers:#[0-9]*::(?P<peers>.*)\nSiblings:#[0-9]*::(?P<siblings>.*)\n")
        myiterator = p.finditer(rd)
        asns = {}
        for match in myiterator:
            asn_ = match.group('asn')
            if asn_ is None: print "AS number is None! why?"
            prvdrs = Set(re.split(r'\D', match.group('providers')))
            ctmrs = Set(re.split(r'\D', match.group('customers')))
            prs = Set(re.split(r'\D', match.group('peers')))
            sblngs = Set(re.split(r'\D', match.group('siblings')))
            if '' in prvdrs: prvdrs.remove('')
            if '' in ctmrs: ctmrs.remove('')
            if '' in prs: prs.remove('')
            if '' in sblngs: sblngs.remove('')

            asns[asn_] = as_info(asn=asn_, providers=prvdrs, customers=ctmrs, peers=prs, siblings=sblngs)
        return asns

    def customre_cone(self, relationships):
        # we build the customer cones that we need. We need them to find the Guards are the same customer cone
        providers = defaultdict(Set)
        for a in relationships:
            my_providers = relationships[a].providers
            for p in my_providers:
                providers[p] |= Set([a])
        cone = defaultdict(Set)
        customer_to_cone = defaultdict(Set)
        siblings_ases = defaultdict(Set)
        peers_ases = defaultdict(Set)
        for a in relationships:

            tmp_cone = Set([a])  # the AS itself is a part of Cone
            tmp_list = Set([a])
            # if a == '3741':
            #    print 'here'
            # Now we want to add up it's constomers and customer's customers
            seens = Set([])
            while len(tmp_list) > 0:
                p = tmp_list.pop()
                # print len(tmp_list), p
                if p in providers and p not in seens:
                    tmp_cone |= providers[p]
                    tmp_list |= providers[p]
                seens |= Set([p])
            cone[a] = tmp_cone
            print a, ':', len(tmp_cone)
            # update the cone of each customer in the list
            for i in tmp_cone:
                customer_to_cone[i] |= Set([a])

            # Now sibling relationships
            seens = Set([])
            sibles = (relationships[a].siblings).copy()
            sibles |= Set([a])
            tmp_sibles = relationships[a].siblings | Set([a])
            while len(tmp_sibles) > 0:
                s = tmp_sibles.pop()
                if s not in seens:
                    tmp_sibles |= relationships[s].siblings
                    sibles |= relationships[s].siblings
                seens |= Set([s])
            for s in sibles:
                siblings_ases[s] = sibles

            # Now update the peers
            my_peers = (relationships[a].peers).copy()
            peers_ases[a] = my_peers
            for i in my_peers:
                peers_ases[i] |= Set([a])
        autonomous_systems = {}
        for a in relationships:
            as_tmp = autonomous_system()
            as_tmp.asn = a
            as_tmp.peers = peers_ases[a]
            as_tmp.cone = cone[a]
            as_tmp.siblings = relationships[a].siblings
            as_tmp.siblings_chain = siblings_ases[a]
            as_tmp.hierarchy_providers = customer_to_cone[a]
        print 'DONE'

    def parse_customer_cone(self):
        # parsing customer cones and p2p and p2c relationships

        # we parse the customer cones from caida website

        # Here we extract peer to peer relationships and provider to customers
        # Note that p2p == 1, p2c == -1, and none == 0
        fil = open(os.path.join(self.PATH_TO_DATASET, self.AS_RELATIONSHIPS), 'r')
        rd = fil.read()
        p = re.compile(r"^(?P<provider>[0-9]+)\|(?P<customers>[0-9]+)\|(?P<link>[-1,0]+)\n", re.MULTILINE)
        links = defaultdict(int)
        myiterator = p.finditer(rd)
        all_ases = Set([])
        for match in myiterator:
            prvdrs = match.group('provider')
            ctmrs = match.group('customers')
            link = match.group('link')
            all_ases |= Set([prvdrs])
            all_ases |= Set([ctmrs])
            if link == '-1': links[(prvdrs, ctmrs)] = -1
            if link == '0': links[(prvdrs, ctmrs)] = 0
        providers, customers = self.build_my_graph(links)
        self.all_ases = copy.copy(all_ases)
        self.providers = copy.copy(providers)
        self.customers = copy.copy(customers)
        self.links = copy.copy(links)
        return

    # Build the graph of ASes
    def generate_directed_as_graph(self, asns):
        ##############################################################
        ##############################################################
        #################Building the Directed Graph##################
        ##############################################################
        ##############################################################
        G = nx.DiGraph()  # it's our graph object
        nodes = asns.keys()
        G.add_nodes_from(nodes)

        for asn in asns:
            info = asns[asn]
            c2p = [(asn, i) for i in info.providers if i is not '']
            p2c = [(asn, i) for i in info.customers if i is not '']
            s2s = [(asn, i) for i in info.siblings if i is not '']
            p2p = [(asn, i) for i in info.peers if i is not '']
            # add edges to the graphs
            G.add_edges_from(c2p, weight=CUSTOMER_TO_PROVIDER)
            G.add_edges_from(p2c, weight=PROVIDER_TO_CUSTOMER)
            G.add_edges_from(s2s, weight=SIBLING_TO_SIBLING)
            G.add_edges_from(p2p, weight=PEER_TO_PEER)
        return G

    def build_my_graph(self, links):
        ##############################################################
        ##############################################################
        #################Building the Directed Graph##################
        ##############################################################
        ##############################################################
        G = nx.DiGraph()  # it's our graph object
        # nodes = asns.keys()
        # nodes = [int(i) for i in nodes]
        # G.add_nodes_from(nodes)
        for key in links:
            if links[key] == 0: continue
            provider, customer = key[0], key[1]
            if provider == customer: continue
            G.add_edge(provider, customer)

        # build customer cone
        successors_ = defaultdict(Set)
        for node in G:
            T = G.successors(node)
            successors_[node] = Set(T)

        tmp_cone = defaultdict(Set)
        print "Building Customer Cone..."
        for node in successors_:
            tmp_successors = Set([])
            loop_container = Set([node])

            while (len(loop_container) != 0):
                current_succ = loop_container.pop()
                tmp_successors |= successors_[current_succ]
                tmp_successors |= Set([current_succ])
                if current_succ in successors_[current_succ]: successors_[current_succ] = successors_[
                                                                                              current_succ] - Set(
                    [current_succ])
                loop_container |= successors_[current_succ]
            tmp_cone[node] = copy.copy(tmp_successors)

        print "Customer Cone built!"

        # check customer cone
        print "Checking the customer cone"
        for pro in tmp_cone:
            current_cust = tmp_cone[pro]
            for cust in current_cust:
                assert (len(current_cust & tmp_cone[cust]) == len(tmp_cone[cust])), 'Custmore Cone is not right'
        print "Successfully checked"

        '''
        providers = defaultdict(Set)
        for node in G:
            T = nx.dfs_successors(G,node)
            succ = Set([])
            succ |= Set([node])
            for t in T:
                succ |= Set([t])
                succ |= Set(T[t])
            providers[node] = succ.copy()
        '''
        G = nx.DiGraph()  # it's our graph object
        # nodes = asns.keys()
        # nodes = [int(i) for i in nodes]
        # G.add_nodes_from(nodes)
        for key in links:
            if links[key] == 0: continue
            provider, customer = key[0], key[1]
            if provider == customer: continue
            G.add_edge(customer, provider)
        customers = defaultdict(Set)
        for node in G:
            T = nx.dfs_successors(G, node)
            succ = Set([])
            succ |= Set([node])
            for t in T:
                succ |= Set([t])
                succ |= Set(T[t])
            customers[node] = succ.copy()
        return tmp_cone, customers

    def guard_selection(self, user , multipath):
        if (self.selection == TOR):
            rnd = random.uniform(0.01, self.today_bw)
            tmp_bw = 0.0
            for rly in self.original:
                tmp_rly = rly
                tmp_bw += rly["bandwidth"]
                if tmp_bw >= rnd: break
            '''
            if user['guard'] != None:
                user['pre_guards'] |= Set([user['guard']])
            if user['guard_asn'] != None:
                user['pre_ases'] |= Set([user['guard_asn']])
            user['guard'] = tmp_rly["ip"]
            user['guard_asn'] = tmp_rly["asn"]
            '''
            user[2] = tmp_rly["adversary"]
            '''
            user['guard_bandwidth'] = tmp_rly["bandwidth"]  # FIXME: should be guards' BW not AS
            user['adv_bandwidth'] = tmp_rly["bandwidth"]
            if user['adversary'] == 0:
                user['adv_bandwidth'] = 0.0
            '''
            return

        if (self.selection == AS_BASED):
            logging.debug("Guard set using ASes")
            #
            #      _______________________________
            # -----|select the set according to BW |______________
            #     |_______________________________|              \
            #                                                     \
            #                                                      \
            #                                         ______________\____________________
            #                                        | select the subset according to BW |
            #                                        |___________________________________|
            #                                                        |
            #                                                        |
            #                                                       DONE
            #

            # first we shoulf select the sets based on their bandwidth
            rnd = random.uniform(0.01, self.today_bw)
            tmp_bw = 0.0
            out_ = None
	    # Wladimir multipath case
	    if (multipath>0):
	        rnd_mp = []
		tmp_mp = []
		for i in xrange(0,multipath):
		    rnd_mp.append(random.uniform(0.01, self.today_bw))
	            tmp_mp.append(0.0)
	   	for q in self.today_all:
                    for j in xrange(0,len(tmp_mp)):	
		         tmp_mp[j] += q[1]
			 if tmp_mp[j] >= rnd_mp[j]:
		             out_ = q
	                     break 
            #Wladimir: End multipath

	    else: 
                for q in self.today_all:  # q = (quatna.id,quanta.bw,quanta.adv)
                    tmp_bw += q[1]
                    if tmp_bw >= rnd:
                        out_ = q
                        break

            user[2] = out_[2]
            user[1] = out_[0]
            logging.debug("user attached to %s", user)
        return

    def update_sset_id(self, setid, sset):
        sset_id = sset.id
        subset_id = sset_id.split(classes.DELIMIT)
        sub_id = setid + classes.DELIMIT + subset_id[1]  # AS_randomnumber
        sset.id = sub_id
        d = classes.DELIMIT
        for q in sset.quantum:
            parts = q.id.split(classes.DELIMIT)  # as ssetid qid 1 q
            q.id = sub_id + d + parts[2] + d + parts[3] + d + parts[4]
        return sset.id

    def update_my_guard_set(self, user,counterQ,counterS,counterSS , multipath):
        #############################
        # extract the as set and its sub set
        setid, subsetid, qunataid = self.get_set_subset_quantum(user[1])
        logging.debug("Updating user %s guard set old ones: set Id:%s Sset ID:%s, quanta ID:%s", user[0], setid,
                      subsetid, qunataid)

        if qunataid in self.quanta_to_sset:
            quanta = self.quanta_to_sset[qunataid]  # (subid,qid,qbw,qadv)
            user[1] = quanta[1]  # q.id
            user[2] = quanta[3]  # q.adv
            logging.debug("existing quanta for User: %s", user)
            return


        #############################

        #############################
        #                                  my set?
        #                                  /    \
        #                                 /      \
        #                               YES      NO_____________________________________________________
        #                                |                                                              |
        #                            my subset?                                         ---------------------------------
        #                               /\                                              |                                |
        #                         _____/  \______                          my own and my childeren's cone?       my ancesters's cone
        #                        |               |                                      |                                |
        #                       YES             NO                              /-------------\                          |
        #                        |               |                             /               \                         |
        #                     return             |                           YES               NO                  do I have one?
        #                                  other quanta?                      |                 |                   _____|______
        #                                    /      \                  stick & return     ask your ancestor        /            \
        #                                   /        \                                                            /              \
        #                                 YES        NO                                                         YES              NO
        #                                  |          |                                                          |                |
        #                            stick & return   |                                                 stick to small one        |
        #                                             |                                                                           |
        #                                        Other subsets                                                             select like a new
        #
        #
        #

        # does my set exist in your gaurd set?
        if setid in self.today_sets:  # my set?
            # YES, if my set exists, check whether my subset exists or not?
            tmp_sub = None
            # my subset?
            if subsetid in self.sset_to_quanta:
                # my quanta?
                if qunataid in self.quanta_to_sset:
                    print "we should not be here, it had been checked before"
                    exit()
                else:
                    # pick one of the quantum here
                    all_quantum = self.sset_to_quanta[subsetid]  # [  .... (qid,q.bw,q.adv,sub.bw).....   ]
                    tot_bw = all_quantum[0][3]
                    self.attach_me_to_a_quanta(user, all_quantum, tot_bw)
                    logging.info("change in QUATNA (to %s) for user %s   %d", user[1], user[0],self.user_change_quanta)
                    counterQ.increment()
                    # logging.info("%s:quanta changed: %s",self.date, user)
                    return
            else:
                # my sset is gone, i should stick to another one in my set
                all_quantum = self.set_to_quanta[setid]  # [  .... (qid,q.bw,q.adv,sub.bw).....   ]
                tot_bw = self.today_sets[setid].bandwidth
                self.attach_me_to_a_quanta(user, all_quantum, tot_bw)
                logging.debug("change in SSET (to %s) for user %s", user[1], user[0])
                counterSS.increment()
                # logging.info("%s:sset changed: %s",self.date, user)

                return

        else:  # my set does not exist in the sets
            # first check my current set's customer cone

            if False:
                logging.debug("Oops, we do not have any providers acitve in our sets for user %s", user[0])
                # non of my ancestors are in the sets, go and select like a new user
                self.guard_selection(user, multipath) #Wladimir multipath
                logging.debug("change in SET from scratch (to %s) for user %s", user[1], user[0])
                # logging.info("%s:start fresh: %s",self.date, user)

                return


            logging.debug("apparently user %s's does not exist, we first check its children's cones", user[0])
            cone = self.providers[setid]
            children = [set_ for set_ in self.today_sets if set_ in cone]
            counterS.increment()

            if len(children) != 0:
                logging.debug("Good for user %s we have %d children for his previous guardset ", user[0], len(children))
                # Yes we have sets in my current set's customer cone
                all_quantum = []
                tot_bw = 0.0
                for child in children:
                    all_quantum.extend(self.set_to_quanta[child])
                    tot_bw += self.today_sets[child].bandwidth
                self.attach_me_to_a_quanta(user, all_quantum, tot_bw)
                logging.debug("change in SET went to children (to %s) for user %s", user[1], user[0])
                # logging.info("%s:went to child: %s",self.date, user)
                return




            else:
                logging.debug("Ok, we do not have any children for user %s right now, lets stick to our ancestors ",
                              user[0])
                # we have to select from our ancestors
                # which ASes are my providers?
                providers = self.customers[setid]
                logging.debug("user %s: Providers %s", user[0], providers)
                # which of ansenctors are in common with today sets
                sets = Set(self.today_sets.keys())
                common = Set([i for i in sets if len(self.providers[i] & providers) != 0])

                # FIXME: Right now this gonna set from the list of all sets, because one the providers should be tier one and includes all the sets
                logging.debug("User %s: common providers with current sets %s ", user[0], common)

                if (len(common) == 0):
                    logging.debug("Oops, we do not have any providers acitve in our sets for user %s", user[0])
                    # non of my ancestors are in the sets, go and select like a new user
                    self.guard_selection(user , multipath) #Wladimir multipath
                    logging.debug("change in SET from scratch (to %s) for user %s", user[1], user[0])
                    # logging.info("%s:start fresh: %s",self.date, user)

                    return
                else:
                    logging.debug("Good, we have %d providers (ancestors) for user %s", len(common), user[0])
                    # common = sorted([(i,len(self.providers[i])) for i in common], key= lambda x:x[1])
                    # common = [i[0] for i in common]
                    all_quantum = []
                    tot_bw = 0.0
                    for cm in common:
                        all_quantum.extend(self.set_to_quanta[cm])
                        tot_bw += self.today_sets[cm].bandwidth
                    self.attach_me_to_a_quanta(user, all_quantum, tot_bw)
                    logging.debug("change in SET went to parents (to %s) for user %s", user[1], user[0])
                    # logging.info("%s: went to parents: %s", self.date,user)

                    return

    def attach_me_to_a_set(self, user, set_list):
        # attach the user to the given list of sets
        # it attacks to the sets according to their bandwidth

        bw_tot = 0.0
        for s in set_list:
            bw_tot += self.today_sets[s].bandwidth

        rnd = random.uniform(0.01, bw_tot)
        tmp_bw = 0.0

        # go through the as list
        for set_ in set_list:
            tmp_bw += self.today_sets[set_].bandwidth
            if tmp_bw >= rnd:
                tmp_set = set_
                break

        # now select a sub set
        self.attach_me_to_a_subset(user, tmp_set)
        return

    def attach_me_to_a_subset(self, user, tmp_set):
        # FIXME: right now I attach the user whom his sub sets is died to a random sub set in his set
        # we attach the user to a sub set in the asked set, right now we just attach to the random subset based on bandwidth
        logging.debug("We want to attach to a sub set in set %s", tmp_set)
        set_bw = self.today_sets[tmp_set].bandwidth
        rnd = random.uniform(0.0, set_bw)
        tmp_bw = 0.0
        for sub in self.today_sets[tmp_set].subsets:
            tmp_bw += sub.bandwidth
            if tmp_bw >= rnd:
                sub_tmp = copy.copy(sub)
                break
        logging.debug("The selected sset is %s from set %s", sub_tmp.id, tmp_set)
        self.update_me(user, sub_tmp)
        return

    def attach_me_to_a_quanta(self, user, all_quantum, tot_bw):
        # FIXME: right now I attach the user whom his sub sets is died to a random sub set in his set
        # we attach the user to a sub set in the asked set, right now we just attach to the random subset based on bandwidth
        logging.debug("We want to attach to a the user %s to a guanta", user[0])
        rnd = random.uniform(0.0, tot_bw)
        tmp_bw = 0.0
        q_tmp = None
        for q in all_quantum:  # [  .... (qid,q.bw,q.adv,sub.bw).....   ]
            tmp_bw += q[1]
            if tmp_bw >= rnd:
                q_tmp = q
                break
        logging.debug("The selected sset is %s ", q_tmp[0])

        user[1] = q_tmp[0]  # q.id
        user[2] = q_tmp[2]  # q.adversary

        return

    def update_me(self, user, sub):
        # Update the user info based on the selected subset
        '''
        if user['guard'] != None:  # it should be a list
            user['pre_guards'] |= Set(user['guard'])
        if user['guard_asn'] != None:
            user['pre_ases'] |= user['guard_asn']

        user['guard'] = copy.copy(sub.guards)  # list of guards in this sub sets
        user['guard_asn'] = copy.copy(sub.active_ases)
        user['adversary'] = sub.adversary
        user['adv_bandwidth'] = sub.adv_bandwidth  # TODO: this bandwidth should be divided by quanta
        user['guard_bandwidth'] = self.user_bandwidth(
            sub.bandwidth_list)  # TODO this bandwidth should be divided by quanta
        user['subset_id'] = sub.id
        user['set_id'] = (sub.id).split(classes.DELIMIT)[0]
        '''
        user[2] = sub.adversary
        user[1] = sub.id

    def get_set_subset_quantum(self, id):  # id = (setid_ssetid_quatnaid_1_1)
        parts = id.split(classes.DELIMIT)
        setid = parts[0]
        subsetid = parts[1]
        # subset_id: set_rand_i_q
        # is it in any quanta?
        quanta = parts[2]

        return setid, subsetid, quanta

    def user_bandwidth(self, bw_list):
        return numpy.median(bw_list)

    def get_users(self):
        # here we generate our users
        pool = Pool(classes.PROCESSES)
        all_users = pool.map(set_user, range(self.number_of_users))
        pool.close()
        pool.join()
        # map(self.users_queue.put,all_users)
        # self.users_queue.put('STOP')
        return all_users

    def add_adversary_to_sets(self, name_=None, relays_=None, sets_=None):
        assert (self.AFTER_DAY == '2015-01-01'), "The adversary's guards should be added in the second day"
        if self.AFTER_DAY in name_:
            adversaries = classes.add_adversary(relays_, adv_type=self.ADVERSARY_TYPE, adv_num=self.adv_num,
                                                adv_bw=self.adv_bw_fraction, ASes=sets_)
            logging.debug("We chose %d adversaries to add to the network ", len(adversaries))
            return adversaries
        else:
            return {}

    def update_users_status(self, w, input, output,counterQ,counterS,counterSS , multipath):

        t1 = time.time()
        cnt = 0
        set_change = 0
        sset_change = 0
        quanta_change = 0
        first_set = None
        first_sset = None
        first_quanta = None
        for user in iter(input.get, 'STOP'):

            # print w,user
            if user[1] != None:
                first_set = user[1].split(classes.DELIMIT)[0]
                first_sset = user[1].split(classes.DELIMIT)[1]
                first_quanta = user[1].split(classes.DELIMIT)[2]

            user[2] = 0
            logging.debug("Working on User %s ", user[0])
            # print user.id



            if user[1] == None:
                logging.debug("P:%d: User %s has no guard ", w, user[0])
                self.guard_selection(user , multipath) #Wladimir
            else:
                logging.debug("P:%d: User %s update its guard ", w, user[0])
                self.update_my_guard_set(user,counterQ,counterS,counterSS , multipath)
            output.put(user)
            set_id = user[1].split(classes.DELIMIT)[0]
            self.today_sets[set_id].assigned_users += 1

            # print user.set_id
            # print user.subset_id
            # checking the compromised users and utilization


            if user[2] > 0:
                self.compromise_rate += 1
                cnt += 1
            sec_set = user[1].split(classes.DELIMIT)[0]
            sec_sset = user[1].split(classes.DELIMIT)[1]
            sec_quanta = user[1].split(classes.DELIMIT)[2]

            if first_set != sec_set:
                set_change += 1
            if first_sset != sec_sset:
                sset_change += 1
            if first_quanta != sec_quanta:
                quanta_change += 1

        # print w," time: ",time.time() - t1
        logging.debug("set change : %d, sset_change: %d, quanta_change: %d", set_change, sset_change, quanta_change)
        return

    def multi_processing_single_guard(self, users, relays, total_bw):

        processes = []
        task_queue = Queue()
        results_queue = multiprocessing.JoinableQueue()
        results = []

        # for l in users:
        #    task_queue.put(l)
        map(task_queue.put, users)
        # print "time to put: ",time.time() - t_t1

        for l in range(classes.PROCESSES):
            task_queue.put('STOP')

        for w in xrange(classes.PROCESSES):
            p = Process(target=self.core_single_guard, args=(w, task_queue, results_queue, relays, total_bw))
            p.daemon = False
            processes.append(p)
            p.start()
        # print "empty the result queue"
        tmp_list = []
        for r in range(self.number_of_users):
            usr = results_queue.get()
            results_queue.task_done()
            if usr[4] != 0:
                tmp_list.append(usr[3])
            results.append(usr)
            # print "join results_queue"
        results_queue.join()
        task_queue.close()
        results_queue.close()
        assert (len(results) == self.number_of_users), "something is wrong with multiprocessing"

        return users, tmp_list

    def single_guard(self, users, relays, total_bw ,multi_path): # Single guards

        tmp_list = []

        for user in users:
            if user[1] not in relays:
                # assign a guard
                rnd = random.uniform(0.00001, total_bw - 0.00001)
                tmp = 0.0
		#Wladimir
		# for multiple guards by multi-path
		if multi_path > 0:
			rnd_mp = []
			tmp_mp = []			
			for h in xrange (0,int(multi_path)):
				rnd_mp.append(random.uniform(0.00001, total_bw - 0.00001))
				tmp_mp.append(0.0)

			for ip in relays:
				for j in xrange(0,len(tmp_mp)):
					tmp_mp[j] += float(relays[ip]["bandwidth"])
					if tmp_mp[j] >= rnd_mp[j]:
						user[1] = ip
		               			user[2] = relays[ip]["adversary"]
		                		break
			if (user[1] == None):
	    			print "we should assign a guard to this user"
	    			exit(0)			
		else:
		#End Wladimir
		        for ip in relays:
		            tmp += float(relays[ip]["bandwidth"])
		            if tmp >= rnd:
		                user[1] = ip
		                user[2] = relays[ip]["adversary"]
		                break
		        if (user[1] == None):
		            print "we should assign a guard to this user"
		            exit(0)

            if user[2] != 0.0:
                tmp_list.append(user[0])  ## Here the client's guard is controlled by an adversary

        return tmp_list

    def core_single_guard(self, w, input, output, relays, total_bw):
        for user in iter(input.get, 'STOP'):
            if user[3] not in relays:
                # assign a guard
                rnd = random.uniform(0.00001, total_bw - 0.00001)
                tmp = 0.0

                for ip in relays:
                    tmp += float(relays[ip]["bandwidth"])
                    if tmp >= rnd:
                        user[3] = ip
                        user[4] = relays[ip]["adversary"]
                        break
                if (user[3] == None):
                    print "we should assign a guard to this user"
                    exit(0)
            output.put(user)

        return

    def daily_process(self):
        ##############################################################
        ##############################################################
        #################Attach relays to the nodes##################
        ##############################################################
        ##############################################################
        #
        #    _______________          ________________           ____________________         ___________________________
        #   |   add users   |________|  read relays   |_________|  Update the sets   |_______|  Update users' guard sets |
        #   |_______________|        |________________|         |____________________|       |___________________________|
        #
        #

        # here we go forward day by day to see what is going on in the network.
        print("adding users ({0} users)".format(self.number_of_users))
        file_name = "log-f-{0}-a-{1}-u-{2}-m-{3}-ct-{4}-dt-{5}-i-{6}.new.log".format(self.adv_bw_fraction, self.ADVERSARY_TYPE,
                                                                       self.adv_num, self.MINIMUM_SETS,
                                                                       self.CREATE_THRESHOLD, self.DELETE_THRESHOLD, self.interations)


        anon_loging  = False

        time_start = time.time()
        users = self.get_users()
        self.compromised_users = Set([])
        logging.debug("%d users are added to the network", self.number_of_users)

        valid_ases_list = Set(classes.valid_ases()) & self.all_ases  # Set of ASes that we have IP information for them
        self.yesterday_sets = {}

        print classes.adv_to_string(self.ADVERSARY_TYPE)
        self.AFTER_DAY = '2015-01-01'
        logging.debug("adversary's guards will be injected from %s", self.AFTER_DAY)


        day_counter = 0
        target_user_id = None # [str(random.randint(1, 999999999999)), None, 0]
        target_user_set = None
        target_user_status = None
        usr_set = None
        usr_sset = None
        usr_quanta = None
        NAdv = 4


        # ---------------------------------------------------------
        # jamies requirements:
        jamies_users = []
        for i in range(self.number_of_users):
            idx = numpy.random.randint(0, 2, 23)
            jamies_users.append(tuple(idx))

        jamies_users = sorted(jamies_users)
        if anon_loging == True:
            log_file = open(file_name,'a')
            for u in jamies_users:
                log_file.write("JAMIE-USERS:DAY:{0}:U:{1}:\n".format(day_counter,u))
            log_file.close()
        gsTree = algorithm.GuardSetTree()
        jamie_adv = {}
        target_compromised = 0
        jamie_waiting_days = 0
        jamieIamBroken = None

        # ---------------------------------------------------------
        single_guard_users = []
        for i in range(self.number_of_users):
            idx = random.randint(1, 999999999999999)
            single_guard_users.append([str(idx), None, 0])



        counterQ = MyCounter(0)
        counterS = MyCounter(0)
        counterSS = MyCounter(0)
        userCompromised = -1
        advAS = None
        compromiseFlag = 0
        # ---------------------------------------------------------

        test = 0
        for name, relays in classes.all_consensuses(ASes=valid_ases_list):
            t1 = time.time()
            self.date = name
            day_counter += 1

            ##########################################################################################
            ######################################## Add Adversary's guards###########################
            ##########################################################################################
            logging.info("We got %d relays in %s and we are going to add adversaries", len(relays), name)
            if (self.ADVERSARY_TYPE == 10):
                #todo, find supersets and add them here
                adversary = self.add_adversary_to_sets(name_=self.date, relays_=relays, sets_=self.adversarial_ASes)
            elif (self.ADVERSARY_TYPE != 11 and self.ADVERSARY_TYPE != 12):
                adversary = self.add_adversary_to_sets(name_=self.date, relays_=relays, sets_=valid_ases_list)
            else:
                adversary = {}
                logging.info("No adversary added")
            #########################################################################################
            #todo for targeted attack I have to bring another method to add and update the adv guards
            #todo update self.our_adversaries
            #todo jamie's adversary should be updated separately
            #########################################################################################
            if len(adversary) != 0:
                assert (len(self.our_adversaries) == 0), "We assign adversaries only in the first day not every day"
                self.our_adversaries = adversary


            if (self.ADVERSARY_TYPE == 11):
                # first check whether we need to add
                if day_counter == 1:
                    # in the first day we are waiting to assign the guard sets
                    logging.info("Targeted Attack: In the first day we are waiting for the target to pick the guard set")
                    self.our_adversaries = {}


                else:

                    if compromiseFlag == 1: userCompromised += 1

                    assert (len(self.adversarial_ASes) != 0), "The length of adversary should not be zero"
                    if advAS == None:
                        advAS = random.choice(list(self.adversarial_ASes))
                        logging.info("Targeted Attack: Selected adversary AS is %s", advAS)
                    assert (advAS != None), "In the day after first day we should get a advesary AS"


                    if (self.adversarial_bw >= self.DELETE_THRESHOLD):
                        # the target's guard set is still high bandiwidth and does not need more bandwidth, skip
                        logging.info("Targeted Attack: The target's guard set has %f KB/s", float(self.adversarial_bw))
                    else:
                        # There is a chance for the adversary to get into the set
                        if compromiseFlag == 0:
                            compromiseFlag = 1

                        # set the adversary's bw
                        if (self.adversarial_bw >= 0.0 and self.adversarial_bw < self.DELETE_THRESHOLD):
                            # in this case target guard set has lost the bw, we need to get in the repair phase
                            #adv_bw = self.CREATE_THRESHOLD - self.adversarial_bw #todo it should be removed
                            tmp_bw = 0.0
                            for set_ in self.today_sets:
                                for sset in self.today_sets[set_].subsets:
                                    for qa in sset.quantum:
                                        tmp_ases = qa.active_ases
                                        if advAS in tmp_ases:
                                            if qa.bandwidth < self.DELETE_THRESHOLD: tmp_bw += (self.CREATE_THRESHOLD - qa.bandwidth)
                            adv_bw = tmp_bw

                            assert (adv_bw >= 0.0)
                            logging.info("Targeted Attack: attacker needs to add %f KB/s", float(adv_bw))


                        else:
                            # self.adversarial_bw == -1 and we lost the target we only add the few guard and waiting
                            adv_bw = 10000.0
                            logging.info('Targeted Attack: Only %f kB/s added, to see what will happen', adv_bw)





                        if (len(self.our_adversaries) == 0):
                            logging.info("Targeted Attack: we do not have any adversarial guard in the network, add on with %f kB/s", adv_bw)
                            asn = advAS
                            NAdv = 0
                            tmp_bw = 0.0
                            while (tmp_bw <= adv_bw*1.1):
                                name = hexlify(urandom(16))
                                ip = None
                                while (ip == None):
                                    ip = classes.gimme_asn_database(asn)
                                rly = {
                                    "nickname":ip,
                                    "ID": name,
                                    "bandwidth": float(int(10000)),
                                    "coord":None,
                                    "geo": None,
                                    "asn": asn,
                                    "valid": None,
                                    "isExit": True,
                                    "isGuard": False,
                                    "ip": ip,
                                    "adversary": 1
                                }
                                self.our_adversaries[ip] = rly
                                NAdv += 1
                                tmp_bw += float(int(10000))
                            logging.info("Targeted Attack: the added adversarial guards: %d\tADV BW: %f", NAdv, float(tmp_bw))
                        else:
                            assert(len(self.our_adversaries) <= NAdv)
                            logging.info("Targeted Attack: We have %d adversarial gaurds in the network and the target guard set's BW is %f we need to tune the bandwidth", len(self.our_adversaries), float(adv_bw))
                            for adv in self.our_adversaries:
                                self.our_adversaries[adv]["bandwidth"] = float(int((adv_bw*1.1)/float(len(self.our_adversaries))))








            logging.info("%d adversaries are added", len(self.our_adversaries))
            relays = self.merge_two_dicts(relays, self.our_adversaries)  # adds the adversaris to the list of relays



            ##########################################################################################
            ##################################### Jamie's Design #####################################
            ##########################################################################################

            corrupted_gs = dict((g, []) for g in self.our_adversaries)  # needed for jamie's evaluation
            gsTree, compromised_jamie_users, median_bw,jamies_sets, jamie_adv, target_compromised,jamie_waiting_days,jamieIamBroken = algorithm.test_comm_adv_merge(gsTree, relays, corrupted_gs,
                                                                                       jamies_users,day_counter,file_name,anon_loging,
                                                                                       NU=self.number_of_users, KTR=self.DELETE_THRESHOLD,CTR= self.CREATE_THRESHOLD, advs = self.ADVERSARY_TYPE, relays_adv = jamie_adv, IamCompromised = target_compromised, waiting_days=jamie_waiting_days, IamBroken = jamieIamBroken , MP = self.multipath) #Wladimir
            self.jamies_users_compromised |= set(compromised_jamie_users)
            self.jamies_users_compromised_rate = float(len(self.jamies_users_compromised) / float(self.number_of_users))
            self.jamies_median_bw = median_bw
            self.number_jamies_sets = jamies_sets
            t_jamie = time.time()
            print  name, " Jamies' took: ", t_jamie - t1
            if (self.ADVERSARY_TYPE == 12): continue


            ##########################################################################################
            ###################################### Single Guard ######################################
            ##########################################################################################

            bw_relays = [relays[i]["bandwidth"] for i in relays]
            total_bw_relays = sum(bw_relays)
            self.single_guard_median_bw = numpy.median(bw_relays)
            single_guard_users_compromised = self.single_guard(single_guard_users, relays, total_bw_relays , self.multipath)
            self.single_guard_users_compromised |= Set(single_guard_users_compromised)
            self.single_guard_users_compromised_rate = float(
                len(self.single_guard_users_compromised) / float(self.number_of_users))
            # print '   OUT:', self.single_guard_users_compromised
            #print ' rate   ', self.single_guard_users_compromised_rate
            # TODO: skip guards with None in asn in our parser, remove the deletes, anyway fix the attacker part, now work on the single guard
            t_single_guard = time.time()
            print name, " Single Guard took: ", t_single_guard - t_jamie



            ##########################################################################################
            ##################################### AS Design ##########################################
            ##########################################################################################

            # continue
            logging.info("We have %d relays totally", len(relays))
            # exit()
            none_ases = 0
            as_list_tmp = {}
            total_bandwidth = 0.0
            total_ases = Set([])
            total_guards = 0
            relay_bws = []

             ####################################### Extract ASes ####################################
            for sample in relays:
                r = relays[sample]
                relay_bws.append(r['bandwidth'])
                if r['asn'] is None:
                    none_ases += 1
                    continue
                if r['asn'] not in self.all_ases:
                    continue
                if r['asn'] not in as_list_tmp: as_list_tmp[r['asn']] = as_set()
                as_list_tmp[r['asn']].size += 1
                (as_list_tmp[r['asn']].guards).append(r['ip'])
                as_list_tmp[r['asn']].bandwidth += r['bandwidth']
                as_list_tmp[r['asn']].ases |= Set([r['asn']])
                as_list_tmp[r['asn']].id = r['asn']
                as_list_tmp[r['asn']].adversary += r["adversary"]
                as_list_tmp[r['asn']].adv_bandwidth += r["bandwidth"]
                total_bandwidth += r['bandwidth']
                total_ases |= Set([r['asn']])
                total_guards += 1
            # if day_one == 1:
            logging.info('in day %s, we had %d ASes, total bandwidth %f, and total number of guards %d', name,
                          len(as_list_tmp), total_bandwidth, total_guards)
            self.relays_bws = [numpy.percentile(relay_bws,10),numpy.percentile(relay_bws,25),numpy.percentile(relay_bws,50),numpy.percentile(relay_bws,75),numpy.percentile(relay_bws,90),min(relay_bws),max(relay_bws),numpy.median(relay_bws)]
            self.today_bw = total_bandwidth
            self.original = copy.copy(as_list_tmp)
            self.relays = copy.copy(relays)
            if (self.selection == AS_BASED):

                ####################################### Build Guard Set ###############################
                self.today_sets = copy.copy(self.update_and_build_sets(as_list_tmp))
		

                ####################################### Update Guard Set ##############################
                self.final_update()
                self.state = UPDATED

                if day_counter == 1:
                    #################################### First Day Setups ##############################
                    self.first_day_sets = copy.copy(self.today_sets)


                ###############################################################
                ###############################################################
                ###############################################################
                # when we reach here, we are good and we can work on users side
                ###############################################################
                ###############################################################
                ###############################################################
                # the plan is to assign the user to a sub set, each set should have at least one sub set with name ASN_RAND_i_QUANTA
                # 1- select the set
                # 2- select the sub set
                # if the user's guard set is died, search to see its set is alive
                # if alive? assign it to the other sub set
                # if not, select its parent, it there is no parent consider it as fresh user

                ##########################################################################################
                ####################### Client Attachments and Compromise Rats ###########################
                ##########################################################################################
                logging.debug("Update the users' guards ")
                self.compromise_rate = 0

                print '----------------------------------------------------'
                t2 = time.time()
                if test == 0 or True:
                    processes = []
                    task_queue = Queue()
                    results_queue = multiprocessing.JoinableQueue()
                    results = []
                    t_t1 = time.time()
                    map(task_queue.put, users)

                    for l in range(classes.PROCESSES):
                        task_queue.put('STOP')
                    for w in xrange(classes.PROCESSES):
                        p = Process(target=self.update_users_status, args=(w, task_queue, results_queue,counterQ,counterS,counterSS,self.multipath))
                        p.daemon = False
                        processes.append(p)
                        p.start()
                    t4 = time.time()
                    # print "empty the result queue"
                    for r in range(self.number_of_users):
                        usr = results_queue.get()
                        results_queue.task_done()
			#print "checnkin user", usr
                        if usr[2] != 0:
                            #print "compromised user", usr
                            self.compromised_users |= Set([usr[0]])
                        results.append(usr)
                        # logging.info("%s:%s", self.date, usr)
                        # print "join results_queue"
                    # logging.info("%s:comp set:%s", self.date, self.compromised_users)
                    results_queue.join()
                    task_queue.close()
                    results_queue.close()
                    assert (len(results) == self.number_of_users), "something is wrong with multiprocessing"
                    users = results

                self.compromise_rate = float(len(self.compromised_users)) / float(self.number_of_users)
                for s in self.today_sets:
                    self.today_sets[s].utilized = int(
                        ((float(self.today_sets[s].bandwidth) / float(self.today_bw)) - (float(self.today_sets[
                                                                                                   s].assigned_users) / float(
                            self.number_of_users))) * (100.0))

                self.day_by_day_comparison()
                self.user_change_quanta = counterQ.value()
                self.user_change_sset = counterSS.value()
                self.user_change_set = counterS.value()

                self.tmp_sets = copy.copy(self.today_sets)
                self.yesterday_sets = copy.copy(self.today_sets)
                self.yesterday_quantum = copy.copy(self.today_quantum)
                print name, " Our design took: ", time.time() - t_single_guard,self.user_change_quanta


                if (self.ADVERSARY_TYPE == 11):# targeted attack
                    # in the first day just pick a user
                    if day_counter == 1:
                        # select the user and her guard set
                        target_user_id = users[0][0] # [str(random.randint(1, 999999999999)), None, 0]
                        target_user_set = users[0][1]
                        target_user_status = users[0][2]
                        usr_set = target_user_set.split(classes.DELIMIT)[0]
                        usr_sset = target_user_set.split(classes.DELIMIT)[1]
                        usr_quanta = target_user_set.split(classes.DELIMIT)[2]
                        logging.info("Targeted Attack: %s, %s, %d ",target_user_id,target_user_set,int(target_user_status))
                        adv_set = Set([])
                        for set_ in self.today_sets:
                            if set_ == usr_set:
                                for sset in self.today_sets[set_].subsets:
                                    ssid = (sset.id).split(classes.DELIMIT)[1]
                                    if ssid == usr_sset:
                                        for qa in sset.quantum:
                                            qid = (qa.id).split(classes.DELIMIT)[2]
                                            if qid == usr_quanta:
                                                self.adversarial_ASes |= qa.active_ases # attacker should add his guards from one of these ASes
                                                self.adversarial_bw = qa.bandwidth

                        assert (len(self.adversarial_ASes) != 0), "No active AS for this user Set: {0}, Sset:{1}, Quanta: {2}, userID: {3}, target set: {4}, status: {5}??".format(usr_set,usr_sset,usr_quanta, target_user_id, target_user_set, target_user_status)
                        logging.info("Targeted Attack: %d: bandwidth: %f: %s",len(self.adversarial_ASes),float(self.adversarial_bw), self.adversarial_ASes)

                    else: # update the bandwith for that set
                        self.adversarial_bw = -1.0
                        for set_ in self.today_sets:
                            for sset in self.today_sets[set_].subsets:
                                for qa in sset.quantum:
                                    qid = (qa.id).split(classes.DELIMIT)[2]
                                    if qid == usr_quanta:
                                        self.adversarial_bw = qa.bandwidth
                        if self.adversarial_bw == -1.0:
                            logging.info("Targeted Attack: change in guard set: %s\t->%s",target_user_set, users[0][1])

                        logging.info("Targeted Attack: Bandwidth updated: %f",float(self.adversarial_bw))


                if (self.ADVERSARY_TYPE == 11 and target_compromised == 0):
                    assert (len(users) == 1)
                    usr = users[0]
                    if usr[2] != 0:
                        bw = 0.0
                        for ip in self.our_adversaries:
                            bw += self.our_adversaries[ip]["bandwidth"]
                        logging.info("Targeted Attack: The target is compromised: at day:%d\tadv guards:%d\tBW:%f\tDays:%d",day_counter,len(self.our_adversaries),bw, userCompromised)
                        target_compromised = 1
                        log_file = open(file_name,'a')
                        log_file.write("AS-TARGETED-ATTACK:DAY:{0}:N-ADV:{1}:BW:{2}:DAYS:{3}:\n".format(day_counter,len(self.our_adversaries),bw,userCompromised))
                        log_file.close()



                if day_counter % 29 == 1 and anon_loging == True:
                    log_file = open(file_name,'a')
                    for u in single_guard_users:
                        log_file.write("SINGLE:DAY:{0}:USER:{1}:GUARD:{2}:\n".format(day_counter,u[0],u[1]))

                    for u in users:
                        log_file.write("AS-BASED:DAY:{0}:USER:{1}:GUARD:{2}:\n".format(day_counter,u[0],u[1]))


                    #self.quanta_to_sset[self.get_quanta_id(q.id)] = (sub.id, q.id, q.bandwidth, q.adversary)
                    for qnt in self.quanta_to_sset:
                        tmp = self.quanta_to_sset[qnt]
                        log_file.write("BW-AS-BASED-BW:DAY:{0}:Q:{1}:Sub:{2}:BW:{3}:\n".format(day_counter,tmp[1],tmp[0],tmp[2]))
                    for rr in relay_bws:
                        log_file.write("BW-SINGLE-BW:DAY:{0}:Q:0:Sub:0:BW:{1}:\n".format(day_counter, rr))
                    log_file.close()
		


        print "total time: ", time.time() - time_start

    def update_and_build_sets(self, current_consensus_as):
        #
        #
        #          __________________          ________________________           __________________________________________________
        #   ______|  Update the sets |________|   Update the sub sets  |_________|  build new set from broken sets and new elements |__________
        #         |__________________|        |________________________|         |__________________________________________________|
        #
        #
        #





        # Here we first check which ASes exist in the current as-sets then we find the leftover ases and finally we make a set out of the leftovers
        # The way that I want to build sets from the leftovers are not determined yet, first I see whether there is a parent as in the current sets or not

        # Actually updating sets have two parts, updating the current sets in terms of bw, and adding new sets and ASes to the list

        # Go over sets and update their size and bandwidth
        # In following, we just update the bw, no change in the number of sets or adding new sets and ASes
        dead_ases = []
        used_ases = Set([])

        logging.info('Updating the list of AS sets in a new day and we have %d sets', len(self.tmp_sets))
        self.state = UPDATING
        # updates are done based on ases not active_ases, then we should add set itself to the ases in building process
        sset_no1 = 0
        sset_no = 0

        for s in self.tmp_sets:
            size = 0
            bandwidth = 0.0
            guards = []
            adv = 0
            adv_bw = 0.0
            active_ases = Set([])
            this_set = (self.tmp_sets[s].ases).copy()
            sset_no1 += len(self.tmp_sets[s].subsets)
            for a in this_set:
                if a in current_consensus_as:
                    size += current_consensus_as[a].size
                    adv += current_consensus_as[a].adversary
                    adv_bw += current_consensus_as[a].adv_bandwidth
                    bandwidth += current_consensus_as[a].bandwidth
                    guards.extend(current_consensus_as[a].guards)
                    active_ases |= Set([a])
                    used_ases |= Set([a])
            self.tmp_sets[s].size = size
            self.tmp_sets[s].bandwidth = bandwidth
            self.tmp_sets[s].died_guards = copy.copy(self.tmp_sets[s].guards)
            self.tmp_sets[s].guards = copy.copy(guards)
            self.tmp_sets[s].active_ases = copy.copy(active_ases)
            self.tmp_sets[s].ases = copy.copy(Set([s]) | active_ases)
            self.tmp_sets[s].adv_bandwidth = adv_bw
            self.tmp_sets[s].adversary = adv
            if size == 0: dead_ases.append(s)
            if ((size == 0) and (bandwidth != 0.0 or len(active_ases) != 0)):
                print 'Oops why'
        # Now we should delete dead ases
        logging.info('%s set are dead', len(dead_ases))
        for d in dead_ases:
            del self.tmp_sets[d]



        # now update the subsets:
        logging.info('Updating the list of sub sets in a new day')
        for s in self.tmp_sets:  # FIXME: this not correct, does not consider quantization
            for sub in self.tmp_sets[s].subsets:
                sset_no += 1
                size = 0
                bandwidth = 0.0
                guards = []
                adv = 0
                adv_bw = 0.0
                active_ases = Set([])
                this_set = (sub.active_ases).copy()
                for a in this_set:
                    if a in current_consensus_as:
                        size += current_consensus_as[a].size
                        bandwidth += current_consensus_as[a].bandwidth
                        guards.extend(current_consensus_as[a].guards)
                        adv += current_consensus_as[a].adversary
                        adv_bw += current_consensus_as[a].adv_bandwidth
                        active_ases |= Set([a])
                sub.size = size
                sub.bandwidth = bandwidth
                sub.died_guards = copy.copy(sub.guards)
                sub.guards = copy.copy(guards)
                sub.active_ases = copy.copy(active_ases)
                sub.ases = copy.copy(active_ases)
                sub.adversary = adv
                sub.adv_bandwidth = adv_bw
                self.update_quantum(sub, Build=0)

                # self.tmp_sets[s].subsets = copy.copy(self.update_subsets(self.tmp_sets[s].subsets))

        logging.info('Updating subsets before: %d', sset_no1)
        logging.info('Updating subsets after: %d', sset_no)







        # ASes that never used in the current AS list
        leftovers = Set(current_consensus_as.keys()) - used_ases
        logging.info('%s ASes are leftover that we should regroup them', len(leftovers))
        # Check the bw, it should be the same amount of bw that we have
        tot_bw = 0.0
        for i in used_ases:
            tot_bw += current_consensus_as[i].bandwidth
        for j in self.tmp_sets:
            tot_bw -= self.tmp_sets[j].bandwidth
        assert (tot_bw == 0), 'update is wrong! {0}'.format(tot_bw)
        # logging.debug('current total bandwidth is %f',tot_bw)


        # check leftovers should not be in the current list
        logging.info('Adding leftovers to the list for regrouping')
        for l in leftovers:
            assert (l not in self.tmp_sets), 'This set ({0}) exists in the current list '.format(l)
            # We append the leftovers to the current as sets and then run the building as set part to either join the new as to current as sets or add them as new set
            self.tmp_sets[l] = current_consensus_as[l]



        # Now build the new ase
        self.state = REGROUPING
        current_as_sets = self.build_as_sets3()
        return current_as_sets

    def merge_two_dicts(self, x, y):
        '''Given two dicts, merge them into a new dict as a shallow copy.'''
        z = x.copy()
        z.update(y)
        return z

    def build_as_sets3(self):  # (as_list_tmp, ,):
        # build the as sets from the given as list, the as list can be an as set from last iteration
        #                                                                                                 ____________________
        #     _____________________________                                                              | This set should be |
        #  __| sort the all customer cones |                                                             |   our provider     |_____________
        #    |   from smallest to largest  |______                                                       |____________________|             |
        #    |_____________________________|      |                                                            /                     _______|______________
        #                                         |                          _____________________            /                     |  this guard set goes |
        #                            _____________|______________           |check if the found AS|          /                      | under this provider  |
        #                           | Find the smallest cone that|          |  exists in sets     |________YES                      |______________________|
        #                           | includes one of guard ASes |          |_____________________|                                         |
        #                           |____________________________|                    |                                                     |
        #                                         |                     ______________|______________                                _______|_______________
        #                                         |____________________|  check if another guard set |                              | keep going till we    |
        #                                                              | is in the found AS          |                              | we reach out threshold|
        #                                                              |_____________________________|                              |_______________________|
        #                                                             /                                                                     |
        #                                                            /                                                               _______|__________
        #                                            _____________YES                                                               | break big sets   |
        #                                       ____|_______                                                                        |__________________|
        #                                      | Merge them |
        #                                      |____________|




        # sort AS sets descending order, based o n their cone size
        logging.debug('Start building the sets, we have %d sets right now', len(self.tmp_sets))
        logging.debug('Sorting the sets based on their customer cone')

        sorted_as_list = [(i, len(self.providers[i])) for i in self.tmp_sets]
        sorted_as_list = sorted(sorted_as_list, key=lambda x: x[1])
        sorted_as_list = [i[0] for i in sorted_as_list]

        logging.debug('Sorting the providers based on their customer cone size')
        # get the list of providers sorted based on their customer cones
        providers_sizes = [(i, len(self.providers[i])) for i in self.providers]
        providers_sizes = sorted(providers_sizes, key=lambda x: x[1])

        original = copy.deepcopy(self.original)
        as_list_tmp = copy.deepcopy(self.tmp_sets)


        # compute the total bw, we need this for the checking and assertions
        total_bw = self.today_bw

        logging.debug('total bandwidth %f', total_bw)

        flag = 1
        round_ = 0
        while (flag):
            round_ += 1
            current_set = sorted_as_list.pop(0)  # check it important!!!!
            current_ases_in_set = as_list_tmp[current_set].ases
            logging.debug('trying to group AS %s', current_set)
            done = 0
            for provider in providers_sizes:
                provider = provider[0]
                customers = self.providers[provider]
                if (len(customers & current_ases_in_set) < len(current_ases_in_set)):
                    continue
                    # the cone should at least includes me
                    # we should consider the equal case as valid case, we can let equal case pass to the rest of the code
                    # After here we ae sure that the cone includes current set
                #  We may reach here when we do not have other set in the list, take care of this case

                # When we reach here we know that we are in cone and we should check other sets in the cone
                for set_ in sorted_as_list:
                    other_ases = as_list_tmp[set_].ases
                    common_ases = customers & other_ases  # this Cone has some active ASes,we should check they do not consider only myself

                    if (len(common_ases) == len(other_ases)):
                        # This is absolutly a bigger cone that includes me, that is what I need
                        # This is my interest, I have to use this Cone and use it as one of my sets
                        # update the as list and sort it again

                        # check the cone includes the current set
                        assert (len(customers & current_ases_in_set) == len(
                            current_ases_in_set)), 'The cone does not include the current set'
                        logging.debug('%s provider includes %s and %s', provider, current_set, set_)
                        logging.debug('now we check provider %s whether it already exists', provider)



                        # now check this provider is not already in one of our sets
                        for set_2 in sorted_as_list:
                            other_ases_2 = as_list_tmp[set_2].ases
                            # print other_ases_2
                            for as_2 in other_ases_2:
                                if provider == as_2:
                                    logging.debug('Provider %s is in set %s', provider, set_2)
                                    assert ((len(self.providers[provider] & current_ases_in_set) == len(
                                        current_ases_in_set)) and (len(self.providers[provider] & other_ases) == len(
                                        other_ases))), 'This should not happen, we checked it already and worked, provider {0} already contained {1} and {2}'.format(
                                        provider, current_set, set_)
                                    # now check whether the parent (set_2) contains both sets (current_set and set_)
                                    logging.debug('check whether AS %s parent of AS %s contains both sets %s and %s',
                                                  set_2, as_2, current_set, set_)
                                    assert (
                                        (len(self.providers[set_2] & current_ases_in_set) == len(
                                            current_ases_in_set)) and (
                                            len(self.providers[set_2] & other_ases) == len(
                                                other_ases))), 'This should not happen, we checked it already and worked, provider {0} already contained {1} and {2}'.format(
                                        provider, current_set, set_)
                                    logging.debug('Provider %s was already in Set %s, we change current provider to it',
                                                  provider, set_2)
                                    provider = set_2



                        # check two sets, they should not have the common ases
                        assert (len(as_list_tmp[set_].active_ases & as_list_tmp[
                            current_set].active_ases) == 0), 'Oops we have common active ases in {0} and {1}'.format(
                            set_, current_set)
                        assert (len(as_list_tmp[set_].ases & as_list_tmp[
                            current_set].ases) == 0), 'Oops we have common ases in {0} and {1}'.format(set_,
                                                                                                       current_set)
                        test_ases_set_1 = Set([])
                        test_ases_set_2 = Set([])

                        for sub in as_list_tmp[set_].subsets:
                            test_ases_set_1 |= sub.active_ases
                        for sub in as_list_tmp[current_set].subsets:
                            test_ases_set_2 |= sub.active_ases
                        assert (len(
                            test_ases_set_1 & test_ases_set_2) == 0), 'Oops we have common ases in sub sets of {0} and {1}'.format(
                            set_, current_set)

                        # "set_ != current_set"
                        logging.debug("Building a Set for provider %s ", provider)
                        a_set = as_set()  # we build a new set, and attach all ASes to it,
                        # check whether
                        a_set.id = provider
                        a_set.active_ases |= as_list_tmp[set_].active_ases
                        a_set.active_ases |= as_list_tmp[current_set].active_ases
                        assert ((set_ in as_list_tmp[set_].ases) and (
                            current_set in as_list_tmp[current_set].ases)), "Oops! I am not in my own set"
                        a_set.ases |= as_list_tmp[set_].ases
                        a_set.ases |= as_list_tmp[current_set].ases

                        # a_set.guards.extend(as_list_tmp[set_].guards)
                        # a_set.guards.extend(as_list_tmp[current_set].guards)

                        # a_set.died_guards.extend(as_list_tmp[set_].died_guards)
                        # a_set.died_guards.extend(as_list_tmp[current_set].died_guards)

                        a_set.subsets.extend(as_list_tmp[set_].subsets)
                        a_set.subsets.extend(as_list_tmp[current_set].subsets)

                        for sset in a_set.subsets:
                            sset.id = self.update_sset_id(a_set.id, sset)

                        # update the bw

                        # now delete the two sets and a new one
                        logging.debug('removing Sets %s and %s from the list', current_set, set_)
                        del as_list_tmp[set_]
                        del as_list_tmp[current_set]

                        # check the new set is already there
                        logging.debug('Adding AS %s to the list (current length %d)', provider, len(as_list_tmp))
                        if provider not in as_list_tmp:
                            as_list_tmp[provider] = as_set()
                        else:
                            logging.debug('AS %s was already in the list, we just update it', provider)
                        as_list_tmp[provider].id = provider
                        as_list_tmp[provider].active_ases |= a_set.active_ases
                        as_list_tmp[provider].ases |= a_set.ases
                        as_list_tmp[provider].ases |= Set([provider])
                        # as_list_tmp[provider].died_guards.extend(a_set.died_guards)
                        # as_list_tmp[provider].guards.extend(a_set.guards)
                        as_list_tmp[provider].subsets.extend(a_set.subsets)

                        # now update the sorted list
                        sorted_as_list = [(i, len(self.providers[i])) for i in as_list_tmp]
                        sorted_as_list = sorted(sorted_as_list, key=lambda x: x[1])
                        sorted_as_list = [i[0] for i in sorted_as_list]
                        logging.debug('AS %s and %s merged into %s', current_set, set_, provider)

                        # go to the next set
                        done = 1
                        break

                if done == 1:
                    break  # go out of the loop over providers

            ##########################################################################
            ##########################################################################
            ######################## update and check the Sets  ######################
            ##########################################################################
            ##########################################################################

            # update the bw and checking
            logging.debug('updating the bandwidth in the list')
            test = Set([])
            total_bw_tmp = 0.0
            for set_ in as_list_tmp:
                tmp_bw = 0
                active_ases = Set([])
                guards_alive = []
                for as_ in as_list_tmp[set_].ases:
                    if as_ in original:
                        tmp_bw += original[as_].bandwidth
                        active_ases |= Set([as_])
                        guards_alive.extend(original[as_].guards)
                        total_bw_tmp += original[as_].bandwidth
                        assert (as_ not in test), "{Active Set {0} already exists".format(as_)
                        test |= Set([as_])
                as_list_tmp[set_].bandwidth = tmp_bw
                as_list_tmp[set_].active_ases = copy.copy(active_ases)
                as_list_tmp[set_].guards = copy.copy(guards_alive)

                # check subsets
                # TODO: remove it
                for sub in as_list_tmp[set_].subsets:
                    assert (len(sub.active_ases & as_list_tmp[set_].active_ases) == len(
                        sub.active_ases)), "some of active ASes in subset are not in the set {0} ASes are missing".format(
                        -len(sub.active_ases & as_list_tmp[set_].active_ases) + len(sub.active_ases))

            logging.debug('Current total bandwidth %f (list length %d)', total_bw_tmp, len(as_list_tmp))
            # logging.debug('Checking the correctness of the algorithm')
            # test_dic = Counter(test)
            # for i in test_dic:
            #    assert (test_dic[i] == 1), 'Reused AS {0} {1} times'.format(i, test_dic[i])
            assert (total_bw_tmp == total_bw), 'Error in computing bw {0} -> {1} '.format(total_bw_tmp, total_bw)

            ##########################################################################
            ##########################################################################
            ########################      Stop Conditions       ######################
            ##########################################################################
            ##########################################################################
            # CHECK if we need to go into the loop again
            # first rule the number of sets is less than what we need
            logging.debug('Check whether we need to regroup or not')
            if len(as_list_tmp) < self.MINIMUM_SETS:
                logging.debug('We have %d sets that is enough (threshold is %d), stopped in round %d', len(as_list_tmp),
                              self.MINIMUM_SETS, round_)
                flag = 0  # continue
            # second rule, all sets should have more than a threshold bandwidth
            cnt = 0
            for set_ in as_list_tmp:
                if as_list_tmp[set_].bandwidth > self.CREATE_THRESHOLD: cnt += 1
            logging.debug('in round %d, %d sets have bandwidth above threshold %d', round_, cnt,
                          int(self.CREATE_THRESHOLD))
            if cnt == len(as_list_tmp):
                logging.debug('We have %d sets with bandwidth above threshold is %d), stopped in round %d', cnt,
                              int(self.CREATE_THRESHOLD), round_)
                flag = 0

        logging.debug("Now we want to break big Sets")
        # The Idea for breaking the big Sets is to break them if they have a bandwidth more than a threshold BREAK_SET_BW_THRESHOLD

        ##################################################################
        ##################################################################
        ##################################################################

        # TODO: we should re-group the subset in all sets, do not forget to do it

        ##################################################################
        ##################################################################
        ##################################################################

        logging.debug("we are working and got %d sets today , %d common sets", len(as_list_tmp),
                     len(Set(as_list_tmp.keys()) & Set(self.yesterday_sets.keys())))
        self.killed_ssets = 0
        self.created_ssets = 0
        # Here we get the list of all ASes that should be broken
        for set_ in as_list_tmp:
            if as_list_tmp[set_].bandwidth > -1:  # classes.BREAK_SET_BW_THRESHOLD:
                logging.debug("%s set has %d kbps, and should be broken", set_, int(as_list_tmp[set_].bandwidth))
                sub_setlist = self.built_and_update_sub_sets(as_list_tmp[set_])
                assert (len(sub_setlist) != 0), "We should have at least one sub set"
                as_list_tmp[set_].subsets = copy.copy(sub_setlist)


        # this set has some spare bandwidth
        ##################################################################
        ##################################################################
        ##################################################################
        # TODO: Sub sets should taken care of
        # Right now I just want to build sub sets,
        # then I should consider the case that they already there
        ##################################################################
        ##################################################################
        ##################################################################
        # logging.debug("we killed %d ssets and created %d ssets", self.killed_ssets, self.created_ssets)
        return as_list_tmp

    def get_bandwidth(self, group):
        # Goup is a set and data is the list of all AS for today,
        # we want to comoute the total active bandwidth in Group
        total = 0.0
        for s_ in group:
            assert (s_ in self.original), "active As should be into the today's ASes"
            total += self.original[s_].bandwidth
        return total

    def get_subset_name(self, id):
        return id + classes.DELIMIT + str(random.randint(1, 9999999999))

    def change_subset_name(self, sset_id, quantum, quanta):
        subset_id = sset_id.split(classes.DELIMIT)
        sub_id = subset_id[0] + classes.DELIMIT + subset_id[1] + classes.DELIMIT  # AS_randomnumber_
        sub_id += str(quantum) + classes.DELIMIT + str(quanta)

        return sub_id

    def split_bandwidth(self, subset, Threshold=40000):
        bandwidth_chunks = []
        quanta = max(int(math.floor(float(subset.bandwidth) / float(Threshold))), 1)
        for quantum in range(quanta):
            bandwidth_chunks.append((subset.id + classes.DELIMIT + str(quantum + 1) + classes.DELIMIT + str(quanta),
                                     float(subset.bandwidth) / quanta))
        return bandwidth_chunks

    def get_quantum_numbers(self, id):
        return int(id.split(classes.DELIMIT)[4])  # asn_ssetid_qid_i_q

    def get_quanta_id(self, id):
        return id.split(classes.DELIMIT)[2]  # asn_ssetid_qid_i_q

    def update_quanta_id(self, ssetid, qid):
        d = classes.DELIMIT
        return "{0}{1}{2}{3}{4}{5}{6}".format(ssetid, d, qid, d, 1, d, 1)

    def update_quantum(self, subset, Build=1):
        guards = subset.guards
        used_guards = Set([])  # contains the list of used guards
        # 1- update existing qunatum
        # 2- repair the broken guantum with guards in their own active ases
        # 3- repair the broken quantum with left guards in other active ases
        logging.debug("we want to update quantum for subset %s", subset.id)
        total_bandwidth = 0.0
        for quanta in subset.quantum:
            bw = 0.0
            # update the guards list and bandwidth in the quanta list
            # fix the IDs
            d = classes.DELIMIT
            parts = quanta.id.split(d)
            quanta.id = subset.id + d + parts[2] + d + parts[3] + d + parts[4]
            myguards = []
            actives = Set([])
            for g in quanta.guards:
                if g in self.relays:
                    myguards.append(g)
                    bw += self.relays[g]['bandwidth']
                    actives |= Set([self.relays[g]['asn']])
                    used_guards |= Set([g])
            quanta.guards = myguards
            quanta.bandwidth = bw
            total_bandwidth += bw
            quanta.active_ases = actives
            logging.debug("Quanta is fixed with id %s and bandwidth %d and gaurds %d active ases %d", quanta.id,
                          int(quanta.bandwidth), len(quanta.guards), len(quanta.active_ases))

        # assert (total_bandwidth == subset.bandwidth),"{0} == {1}".format(total_bandwidth , subset.bandwidth)
        # update the IDs:
        quantum_list = []
        checked = []
        logging.debug("Total bw = %d subset.bw = %d", int(total_bandwidth), int(subset.bandwidth))

        ''' # we do not need this part because why we need to break them based on bandwidth
        for quanta in subset.quantum:
            if self.get_quanta_id(quanta.id) in checked: continue
            pre_quanta = self.get_quantum_number(quanta.id)
            cur_quanta  = max(int(math.floor(float(quanta.bandwidth) / float(self.CREATE_THRESHOLD))), 1)
            logging.debug("for %s quanta We had %d quanta, but now we have %d", quanta.id, pre_quanta, cur_quanta)
            checked.append(self.get_quanta_id(quanta.id))
            for q in range(cur_quanta):
                Q = Quanta()
                Q.bandwidth = float(quanta.bandwidth)/float(cur_quanta)
                Q.guards = copy.copy(quanta.gaurds)
                used_guards |= Set(Q.guards)
                Q.active_ases |= quanta.active_ases
                Q.id = self.update_quanta_id(Q.id,q+1,cur_quanta)
                quantum_list.append(Q)
                logging.debug("One Quanta updated, under id: %s, with bandwidth: %d", Qid, int(Q.bandwidth))

        '''
        assert (self.DELETE_THRESHOLD < self.CREATE_THRESHOLD), "Deletion bw should be less than creation"
        logging.debug("build is %d", Build)
        # now repair the quantum
        if Build == 0:
            return
        # first use guards on my own active ases to save the dead quantum
        for quanta in subset.quantum:
            if quanta.bandwidth > self.DELETE_THRESHOLD: continue
            myacitves = quanta.active_ases
            possible_guards = [g for as_ in myacitves for g in self.original[as_].guards]
            left_guards = Set(possible_guards) - used_guards  # Set(quanta.guards)
            left_guards = [(g, self.relays[g]['asn']) for g in left_guards]
            left_guards.sort(key=lambda x: x[1])
            logging.debug("There are %d guards lelft that we can save quanta %s", len(left_guards), quanta.id)
            while ((quanta.bandwidth < self.CREATE_THRESHOLD) and (len(left_guards) != 0)):
                chosen_guard = (left_guards.pop())[0]
                quanta.bandwidth += self.relays[chosen_guard]["bandwidth"]
                quanta.guards.append(chosen_guard)
                logging.debug("guard %s added to %s ", chosen_guard, quanta.id)
                used_guards |= Set([chosen_guard])

        unused_guards = Set(subset.guards) - used_guards
        unused_guards = [(g, self.relays[g]['asn']) for g in unused_guards]
        unused_guards.sort(key=lambda x: x[1])
        logging.debug("%d unused guards we have", len(unused_guards))
        for quanta in subset.quantum:
            # now if we are dead, use other ASes to save the quanta
            if quanta.bandwidth > self.DELETE_THRESHOLD: continue
            while ((quanta.bandwidth < self.CREATE_THRESHOLD) and (len(unused_guards) != 0)):
                chosen_guard = unused_guards.pop()
                quanta.bandwidth += self.relays[chosen_guard[0]]["bandwidth"]
                quanta.guards.append(chosen_guard[0])
                quanta.active_ases |= Set([chosen_guard[1]])
                used_guards |= Set([chosen_guard[0]])
                logging.debug("guard %s added to %s ", chosen_guard, quanta.id)

        unused_guards = Set(subset.guards) - used_guards
        logging.debug(
            "we repaired the quantum, now we want to build new ones, we have %d leftover guards from total %d guards",
            len(unused_guards), len(subset.guards))

        bw = 0.0
        tmp_set = Set([])
        chunks = []
        # first separate big ases and save them in chunks var
        for as_ in subset.active_ases:
            left_guards = Set(self.original[as_].guards) - used_guards
            bw = self.get_bandwidth_from_relays(left_guards)
            # tmp_set = Set([as_])
            if bw > self.CREATE_THRESHOLD:
                chunks.append(as_)
                logging.debug("AS %s has enough bandwidth (%d kBs)", as_, int(bw))

        bw = 0.0
        tmp_set = Set([])
        logging.debug("chucks more that create threshold %s total active ases are %d", Set(chunks),
                      len(subset.active_ases))
        leftover = subset.active_ases - Set(chunks)
        leftover = Set([as_ for as_ in leftover if
                        self.get_bandwidth_from_relays(Set(self.original[as_].guards) - used_guards) > 0.0])

        chunks = [Set([as_]) for as_ in chunks]
        used = Set([])
        logging.debug(" we have %d ASes above the threshold, %d leftover", len(chunks), len(leftover))
        for as_ in leftover:
            left_guards = Set(self.original[as_].guards) - used_guards
            tmp_bw = self.get_bandwidth_from_relays(left_guards)
            logging.debug("for AS %s we have %d guards left bw: %d,(total: %d guards)", as_, len(left_guards),
                          int(tmp_bw), len(Set(self.original[as_].guards)))
            if tmp_bw > 0.0: tmp_set |= Set([as_])
            bw += tmp_bw
            if bw > self.CREATE_THRESHOLD:
                chunks.append(tmp_set)
                bw = 0.0
                used |= tmp_set
                logging.debug("we have  %s ASes which have enough bandwidth %d, we addd them", tmp_set, int(bw))
                tmp_set = Set([])
        logging.debug("We could find %d ASes which can be in the same spot", len(used))
        leftover = leftover - used
        logging.debug("now we have %s ASes left", leftover)

        # print chunks
        try:
            chunks[-1] |= leftover
        except:
            if len(leftover) != 0:
                chunks.append(Set([]))
                chunks[-1] |= leftover

        logging.debug("we got %s sets of ASes that we can build qunatum", chunks)

        qunatum = []
        for comb in chunks:
            # build quanta for this combination
            qunatum.extend(self.build_quantum(subset, comb, used_guards))

        logging.debug("we have %d quantum for subset %s", len(qunatum), subset.id)
        logging.debug("subset %s had %d quantum, now we will add %d", subset.id, len(subset.quantum), len(qunatum))
        subset.quantum.extend(qunatum)
        logging.debug("Now, subset %s has %d quantum", subset.id, len(subset.quantum))

        ############################Testing###########################

        all_guards = Set([])
        bw = 0.0
        for q in subset.quantum:
            all_guards |= Set(q.guards)
            bw += q.bandwidth
        assert ((bw == subset.bandwidth) and (len(all_guards & Set(subset.guards)) == len(
            all_guards))), "something is wrong {0} == {1} and {2} == {3}".format(bw, subset.bandwidth,
                                                                                 len(all_guards & Set(subset.guards)),
                                                                                 len(all_guards))
        ############################Testing###########################

        return

    def get_bandwidth_from_relays(self, guards):
        return float(sum([self.relays[g]['bandwidth'] for g in guards]))

    def list_all_guard_quanta(self, guards, min_allowance=0):
        quanta = []
        for guard in guards:
            #chunks = max(int(math.floor(float(self.relays[guard]['bandwidth']) / Threshold)), 1)
            chunks = 1
            for Q in range(chunks):
                quanta += [(guard, Q, chunks, float(self.relays[guard]['bandwidth']), self.relays[guard]['asn'],
                            float(self.relays[guard]['bandwidth']) / float(chunks))]
        return quanta

    def set_quanta_id(self, subid, i, q):
        d = classes.DELIMIT
        return "{0}{1}{2}{3}{4}{5}{6}".format(subid, d, random.randint(0, 99999999999999), d, i, d,
                                              q)  # asn_subid_qid_i_q

    def form_guantum_set(self, subset, chunks):
        # TODO:
        chunks.sort(key=lambda x: x[4])  # sort based on asn
        our_sets = []
        multi_quanta = []

        bw = 0.0
        tmp_set = Set([])
        guard_list = []

        while len(chunks) > 0:
            quanta = chunks.pop()
            logging.debug("we added a guard %s with bandwidth %d to a quanta", quanta[0], int(quanta[5]))

            if quanta[5] > self.CREATE_THRESHOLD:
                Q = Quanta()
                Q.bandwidth = quanta[5]
                Q.guards = [quanta[0]]
                Q.active_ases |= Set([quanta[4]])
                Q.id = self.set_quanta_id(subset.id, 1, 1)
                logging.debug("we added a quanta id: %s, bandwidth:%d, guards: %d, ASes: %d*", Q.id, int(Q.bandwidth),
                              len(Q.guards), len(Q.active_ases))
                our_sets.append(Q)
            else:
                bw += quanta[5]  # bandwidth fraction
                tmp_set |= Set([quanta[4]])
                guard_list.append(quanta[0])
                if bw > self.CREATE_THRESHOLD:
                    Q = Quanta()
                    Q.bandwidth = bw
                    bw = 0.0
                    Q.guards = copy.copy(guard_list)
                    guard_list = []
                    Q.active_ases |= tmp_set
                    tmp_set = Set([])
                    Q.id = self.set_quanta_id(subset.id, 1, 1)
                    logging.debug("we added a quanta id: %s, bandwidth:%d, guards: %d, ASes: %d", Q.id,
                                  int(Q.bandwidth),
                                  len(Q.guards), len(Q.active_ases))
                    our_sets.append(Q)

        # we have to take care of left overs:
        try:
            Q = copy.copy(our_sets[-1])
        except:
            Q = Quanta()

        Q.bandwidth += bw
        Q.active_ases |= tmp_set
        Q.guards.extend(guard_list)
        Q.id = self.set_quanta_id(subset.id, 1, 1)

        try:
            del our_sets[-1]
        except:
            pass

        our_sets.append(Q)
        logging.debug(
            "we add leftover to the last quanta (%s bw: %d guards %d) in the quanta list we have right now %d quatnum, ",
            Q.id, int(Q.bandwidth), len(Q.guards),
            len(our_sets))
        assert (len(multi_quanta) == 0), "it should not reach here"
        # now add bih qunata
        trash_dic = {}
        for quanta in multi_quanta:
            if quanta[0] not in trash_dic: trash_dic[quanta[0]] = [0, quanta[2], None]  # ()
            trash_dic[quanta[0]][0] += 1
            if trash_dic[quanta[0]][2] == None:
                myid = self.set_quanta_id(subset.id, trash_dic[quanta[0]][0], trash_dic[quanta[0]][1])
                trash_dic[quanta[0]][2] = myid
            else:
                myid = selfupdate_quanta_id(trash_dic[quanta[0]][2], trash_dic[quanta[0]][0], trash_dic[quanta[0]][1])

            Q = Quanta()
            Q.id = myid
            Q.guards.append(quanta[0])
            Q.active_ases |= Set([quanta[4]])
            Q.bandwidth = quanta[5]
            our_sets.append(Q)
            logging.debug("we added a big quanta id: %s, bandwidth: %d, IP:%s ", Q.id, int(Q.bandwidth), Q.guards[0])

        logging.debug(" total quantum in the subset %d", len(our_sets))
        return our_sets

    def build_quantum(self, subset, comb, used_guards):

        logging.debug("AS combinations in sub set %s for building quantum: %s", subset.id, comb)
        all_guards = Set([])
        for as_ in comb:
            all_guards |= (Set(self.original[as_].guards) - used_guards)

        chunks = self.list_all_guard_quanta(all_guards)
        logging.debug("all guards in here: %d and we have %d quantum", len(all_guards), len(chunks))
        formed_quantum = self.form_guantum_set(subset, chunks)
        logging.debug("retuned quantum %d", len(formed_quantum))
        return formed_quantum

    def update_subsets(self, subs, setid, Build=0):
        """
        we are supposing that all active_ases are already checked and are in the list
        the active ases are already updated from the last part
        """
        alive_sub_sets = []
        # subsets = copy.copy(subs)
        logging.debug("We want to update sub sets (subsets)")
        bw = 0.0
        for sub in subs:
            assert (setid in sub.id), ""
            bw = 0.0
            for as_ in sub.active_ases:
                bw += self.original[as_].bandwidth
            sub.bandwidth = bw
            self.update_quantum(sub, Build)
            assert (len(sub.quantum) != 0), "subset should have at least one quanta"
            test_bw = 0.0
            test_ases = Set([])
            for q in sub.quantum:
                test_bw += q.bandwidth
                test_ases |= q.active_ases
                assert (sub.id in q.id)
                logging.debug("existing quantum: id:%s\tbw:%d\tguards:%d\tASes:%s", q.id, int(q.bandwidth),
                              len(q.guards), q.active_ases)
            if (Build == 1):
                assert ((test_bw == sub.bandwidth)) and (
                    len(test_ases) == len(sub.active_ases)), "{0} == {1} and {2} == {3}".format(test_bw, sub.bandwidth,
                                                                                                len(test_ases),
                                                                                                len(sub.active_ases))
        return

    def update_active_ases_in_sset(self, set_):
        # in here, we find active ases that can be fitted in one of our current subsets, we
        # attach them to the subset with provider which has the active as in its cone
        logging.debug("we are gonna to update the list of active ASes in the sub-sets")
        grouped = Set([])
        tmp_dict = {}
        used_sets = Set([])
        for sub in set_.subsets:
            used_sets |= sub.active_ases
        for sub in set_.subsets:
            # print "We got this sset: ", sub.provider, sub.id
            if sub.provider == None: continue
            common = (self.providers[sub.provider] & set_.active_ases) - used_sets
            # common = common - sub.active_ases
            assert (len(self.providers[sub.provider] & sub.active_ases) == len(
                sub.active_ases)), 'Print active_ases are not in the cone?'
            # if (len(self.providers[sub.provider] & set_.active_ases) == len(sub.active_ases)): continue
            if len(common) == 0: continue
            # print "orginal:", sub.id,sub.active_ases
            if len(grouped & common) == 0:
                logging.debug("OoO we could attach %d new active ASes to sub set %s, these new ASes are %s ",
                              len(common), sub.id, common)
                grouped |= common
                tmp_dict[sub.give_sset_id()] = common
            else:
                logging.debug("Common:%s\tgrouped:%s\tsub.actives:%s", common, grouped, sub.active_ases)
                # for  p in tmp_dict:
                #	logging.debug("our tmp dict:\t%s:\ts%s",p,tmp_dict[p])
                # assert (common <=  tmp_dict[sub.give_sset_id()]), "Active ASes {0} they are attached to the different subset, but we have this {1}, with active sets {2}  ".format(common,tmp_dict[sub.give_sset_id()], sub.active_ases)

        for sub in set_.subsets:
            myid = sub.give_sset_id()
            if myid in tmp_dict:
                # print "Before:", myid,sub.active_ases
                sub.active_ases |= tmp_dict[myid]
                sub.ases |= tmp_dict[myid]
                for a_as in tmp_dict[myid]:
                    sub.guards.extend(self.original[a_as].guards)
                    # print "After: ",myid,sub.active_ases
            sub.bandwidth = self.get_bandwidth(sub.active_ases)
            assert (sub.id != None), "checked"
        # print '---------------------------'

        return

    def built_and_update_sub_sets(self, set_):  # , providers, original):
        # first let's update the subsets
        # approach: go through all the sub sets and then if their bw had been dropped too much release their ASes, to re-group them again

        ###### active_ases should be updated already ###########################
        # active_ases = copy.copy(set_.active_ases)
        #          ________________________
        #     ____| Update the current     |
        #         | subsets, killed low BW |___________
        #         |________________________|            |
        #                                               |
        #                                      _________|____________
        #                                     |  build new sub set   |
        #                                     | from the leftovers   |
        #                                     |______________________|
        #
        #
        #
        #
        #
        #

        # ---------------------------------------------------------------#


        deleted_sub_sets = []
        active_ases_released = Set([])  # contains the list of ASes that we do *not need* to re-group them
        alive_sub_sets = []
        logging.debug(" We want to split AS set%s and update sub sets, we have %d ssets, and total BW %d", set_.id,
                      len(set_.subsets), int(set_.bandwidth))

        self.update_active_ases_in_sset(set_)  # THIS IS FINE, because we just change active_ases
        # self.update_subsets(set_.subsets, set_.id)  # FIXME: THIS NEEDS CHANGE
        subsets = copy.copy(set_.subsets)
        logging.debug("after updating ssets, we have %d ssets", len(subsets))



        # find the low bandwidth subsets an kill them release their active ases
        for sub in subsets:  # TODO: check whether subsets are updated or not, in terms of bw, active ases
            if sub.bandwidth < self.DELETE_THRESHOLD:
                deleted_sub_sets.append(sub.id)
                active_ases_released |= sub.active_ases

        if ((len(deleted_sub_sets) == 1 and len(set_.subsets) == 1) and (
                    len(active_ases_released) == len(set_.active_ases))):
            final_list = copy.copy(subsets)
            logging.debug(" Subset is not needed to be deleted we can are good,")
            self.update_subsets(final_list, set_.id, Build=1)  # FIXME
        else:
            for d in deleted_sub_sets:
                for s in subsets:
                    if d == s.id:
                        logging.debug(" Subset %s is deleted due to the low bw %d", s.id, int(s.bandwidth))
                        subsets.remove(s)
                        break
            logging.debug("we kill %d (still have %d) subsets which deleted are %s", len(deleted_sub_sets),
                          len(subsets),
                          deleted_sub_sets)
            # self.killed_ssets += len(deleted_sub_sets)

            # check we are correct or not,
            active_used_ases = Set([])
            for sub in subsets:
                active_used_ases |= sub.active_ases
            active_ases = set_.active_ases - active_used_ases
            logging.debug("we released %s, totally had %d, and used %d, so left overs %d (%s) ", active_ases_released,
                          len(set_.active_ases), len(active_used_ases), len(active_ases), active_ases)

            logging.debug("We have %d active ASes that we should take care of, and we have %d subset ready",
                          len(active_ases), len(subsets))
            assert (((active_ases | active_used_ases) >= set_.active_ases) and ((
                                                                                    active_ases | active_used_ases) <= set_.active_ases)), "mismatch in leftover active ASes leftovers:{0}, used:{1}, all:{2} ".format(
                active_ases, active_used_ases, set_.active_ases)


            # ---------------------------------------------------------------#
            # for sub in subsets:
            #    logging.debug("2 Subset ID: %s\t%d\tAS:%s",sub.id, sub.bandwidth,sub.active_ases)
            # logging.debug("all actives:%s",set_.active_ases)
            # logging.debug("released actives:%s",active_ases_released)
            # logging.debug("used actives:%s",active_used_ases)
            # logging.debug("leftover actives:%s",active_ases)


            # logging.debug("all BW:%d",int(sum([self.original[i].bandwidth for i in set_.active_ases])))
            # logging.debug("released BW:%d",int(sum([self.original[i].bandwidth for i in active_ases_released])))
            # logging.debug("used BW:%d",int(sum([self.original[i].bandwidth for i in active_used_ases])))
            # logging.debug("leftover BW:%d",int(sum([self.original[i].bandwidth for i in active_ases])))

            # ---------------------------------------------------------------#



            sub_sets_list = []
            grouped = Set([])  # list of used active ASes
            if (self.get_bandwidth(active_ases) > self.CREATE_THRESHOLD_SSET):
                # now we have the updated list of subsets (alive_sub_sets) and the list of active ASes (active_ases) ready to be grouped
                # Here I just build subsets, then I rewrite it
                customers = self.providers[set_.id]  # we get the customer cone
                sub_active_cone = []  # contains list of sub cone of parent cone that contain the active ASes
                active_high_bw_cone = Set(
                    [])  # contains list of sub cone have high bw ( greadter than CREATE_SUB_SET_BANDWIDTH_THRESHOLD)

                for cust in customers:
                    sub_customers = self.providers[cust]
                    common = active_ases & sub_customers  # common ASes between active ASes in this set and the current sub cone
                    if len(common) == 0: continue
                    sub_active_cone.append((common, len(sub_customers), cust))  # FIXME: common or sub_customers?
                    current_sub_cone_bw = self.get_bandwidth(common)
                    if (current_sub_cone_bw > self.CREATE_THRESHOLD_SSET):
                        active_high_bw_cone |= Set(
                            [(cust, current_sub_cone_bw)])  # FIXME: This needs to be thought more
                sub_active_cone = sorted(sub_active_cone,
                                         key=lambda x: x[1])  # Sort the active cone based on their size
                # TODO: be careful about the set itself in the its cone
                logging.debug("We have %d possible cones that can group them", len(sub_active_cone))
                logging.debug("We have %d cones with bandwidth greater than %d", len(active_high_bw_cone),
                              int(self.CREATE_THRESHOLD_SSET))

                # Go through the active sub cones and look for ones that have more than threshold bandwidth, these should be separate sets


                # Now I want to find all customer cones that they have enough bandwidth ( greadter than CREATE_SUB_SET_BANDWIDTH_THRESHOLD)
                if True:
                    # in here we want to find all combinations and then find the one that includes either more bandwidth or more active cones
                    # this process may be time consuming
                    all_acitve_providers = [sub.provider for sub in subsets if
                                            sub.provider != None]  # contrains all subsets' providers
                    all_acitve_providers = all_acitve_providers + [as_ for sub in subsets if sub.provider == None for
                                                                   as_ in
                                                                   sub.active_ases]  # TODO: check this out
                    # logging.debug("we have %d subset providers which are:\n%s", len(all_acitve_providers),all_acitve_providers)
                    # logging.debug("we have %d active cone which are:\n%s", len(active_high_bw_cone),active_high_bw_cone)
                    active_high_bw_cone = [i for i in active_high_bw_cone if len(
                        [j for j in all_acitve_providers if len(self.providers[i[0]] & self.providers[j]) != 0]) == 0]
                    logging.debug("but after pruning we have %d active cone, which are:\n%s", len(active_high_bw_cone),
                                  active_high_bw_cone)
                    all_combinations = Set([])
                    for i in active_high_bw_cone:
                        all_combinations |= Set([Set([i])])

                    new_combinations = Set(
                        []) | all_combinations  # here we contains the new combinations that we want to add to all_combinations

                    while True:
                        tmp = Set([])
                        for this_comb in new_combinations:
                            size = len(this_comb)
                            for this_cone in active_high_bw_cone:
                                count = 0
                                for ele in this_comb:
                                    if (len(self.providers[ele[0]] & self.providers[this_cone[0]]) == 0):
                                        count += 1
                                if count == size:
                                    # we can add a new combination, add this cone to this current combination

                                    tmp |= Set([ImmutableSet(this_comb | ImmutableSet([this_cone]))])

                                    # new_combinations[-1].append(this_cone)
                        if len(tmp) == 0:
                            break
                        new_combinations = Set([]) | tmp
                        all_combinations |= tmp
                    best_combination = []
                    if len(all_combinations) != 0:
                        best_combination = max(all_combinations, key=lambda x: len(x))
                    logging.debug("We could found %s unique combinations", all_combinations)
                    logging.debug("The best combination that we could find has %s", best_combination)

                    for ele in best_combination:
                        cone = self.providers[ele[0]]
                        provider = ele[0]
                        current_sub_cone_bw = ele[1]

                        # find the active as in the cone:
                        common = cone & set_.active_ases
                        # their bandwidth is more than threshold we already checked this in the above loop
                        assert (len(common) != 0), "How come this cone does not have any active ASes"

                        sub_set = Subset()
                        sub_set.bandwidth = current_sub_cone_bw
                        sub_set.id = self.get_subset_name(set_.id)  # FIXME
                        logging.debug(
                            "We found sub-set id:%s with bw:%d from our customer cones, and provider is set to %s",
                            sub_set.id,
                            int(sub_set.bandwidth), provider)
                        sub_set.provider = provider

                        for as_in_sub_set in common:
                            grouped |= Set([as_in_sub_set])
                            sub_set.active_ases |= Set([as_in_sub_set])
                            sub_set.ases |= Set([as_in_sub_set])
                            sub_set.guards.extend(self.original[as_in_sub_set].guards)

                        sub_sets_list.append(sub_set)






                else:

                    for current_sub_cone in sub_active_cone:
                        provider = current_sub_cone[2]
                        current_sub_cone = current_sub_cone[0]  # they are active ASes
                        current_sub_cone_bw = self.get_bandwidth(current_sub_cone)
                        if ((current_sub_cone_bw > self.CREATE_THRESHOLD_SSET) and (
                                    len(grouped & current_sub_cone) == 0)):
                            # So this can be sub set
                            sub_set = Subset()
                            sub_set.bandwidth = current_sub_cone_bw
                            sub_set.id = self.get_subset_name(set_.id)
                            sub_set.provider = provider
                            logging.debug("We found sub-set id:%s with bw:%d from our customer cones", sub_set.id,
                                          int(sub_set.bandwidth))
                            for as_in_sub_set in current_sub_cone:
                                grouped |= Set([as_in_sub_set])
                                sub_set.active_ases |= Set([as_in_sub_set])
                                sub_set.ases |= Set([as_in_sub_set])
                                sub_set.guards.extend(self.original[as_in_sub_set].guards)

                            sub_sets_list.append(sub_set)

            not_grouped_active_ases = active_ases - grouped
            logging.debug("we still have %d active ASes that we should group them", len(not_grouped_active_ases))
            leftover_bw = self.get_bandwidth(not_grouped_active_ases)
            logging.debug("Let's group them by BW, we have %d KBps", int(leftover_bw))
            if len(not_grouped_active_ases) != 0:
                sub_set = Subset()
                sub_set.bandwidth = leftover_bw
                sub_set.id = self.get_subset_name(set_.id)  # FIXME
                sub_set.provider = None
                logging.debug("We add this sub-set id:%s with bw:%d from the leftovers", sub_set.id,
                              int(sub_set.bandwidth))
                for as_in_sub_set in not_grouped_active_ases:
                    grouped |= Set([as_in_sub_set])
                    sub_set.active_ases |= Set([as_in_sub_set])
                    sub_set.ases |= Set([as_in_sub_set])
                    sub_set.guards.extend(self.original[as_in_sub_set].guards)
                # build a sub set out of this leftovers
                sub_sets_list.append(sub_set)

            self.created_ssets += len(sub_sets_list)
            # add updated subsets to the new ones
            final_list = []
            nones = []
            none_id = None
            for sub in subsets:
                if sub.provider == None:
                    logging.debug("Subset %s has provider NONE", sub.id)
                    none_id = sub.id
            subsets.extend(sub_sets_list)
            # unify the sub sets with provider == None:
            for sub in subsets:
                if sub.provider == None:
                    nones.append(sub)
                    logging.debug("after concatenation: Subset %s has provider NONE", sub.id)

                else:
                    final_list.append(sub)

            if len(nones) > 0:
                logging.debug("%d subsets with None in their providers, %s was the existing None-provider", len(nones),
                              none_id)
                sub_set = Subset()
                sub_set.id = self.get_subset_name(set_.id)
                if none_id != None: sub_set.id = none_id
                for none in nones:
                    sub_set.active_ases |= none.active_ases
                    sub_set.ases |= none.ases
                    sub_set.guards.extend(none.guards)
                    sub_set.quantum.extend(none.quantum)
                sub_set.guards = list(Set(sub_set.guards))
                sub_set.bandwidth = self.get_bandwidth(sub_set.active_ases)
                assert (sub_set.id != None), "subset id is NONE???"
                final_list.append(sub_set)

            logging.debug("Now we want to split the bandwidth in each sub set")

            self.update_subsets(final_list, set_.id, Build=1)  # FIXME

            logging.debug("Now we got %d subset for Set %s", len(sub_sets_list), set_.id)


            # ---------------------------------------------------------------#
            # for sub in subsets:
            #    logging.debug("Now Subset ID: %s\t%d",sub.id, sub.bandwidth)
            #    assert (sub.id != None), "third check"

            # ---------------------------------------------------------------#



            # merge the subsets which have overlape
            # self.merge_subsets(subsets)




        # Now check the bandwidth to see whether or not everything is fine
        bw_tmp = 0.0
        active_ases = Set([])
        for subset in final_list:
            bw_tmp += subset.bandwidth
            active_ases |= subset.active_ases
        logging.debug("we checked the built subsets, they seems fine, no change in bw (%d,%d)", bw_tmp, set_.bandwidth)
        assert ((abs(bw_tmp - set_.bandwidth) < 10) and (len(active_ases) == len(set_.active_ases))), (
            "We did not break the set, bw was {0}, now is {1} nad ative ASes was {2} and now {3}".format(
                int(set_.bandwidth), int(bw_tmp), len(set_.active_ases), len(active_ases)))
        logging.debug("we checked the built subsets, they seems fine, no change in bw (%d,%d)", bw_tmp, set_.bandwidth)

        return final_list

    def merge_subsets(self, subsets):

        subset_list = []
        while len(subsets) > 0:
            sub = subsets.pop()

    def day_by_day_comparison(self):
        yesterday_bw = 0.0
        yesterday_sets = self.yesterday_sets.keys()
        yesterday_active = Set([])

        day_one_bw = 0.0
        day_one_sets = self.first_day_sets.keys()
        day_one_active = Set([])

        today_bw = 0.0
        today_sets = self.today_sets.keys()
        today_active = Set([])

        utilized = []

        yesterday_ssets = Set([])
        for s in self.today_sets:
            today_bw += self.today_sets[s].bandwidth
            today_active |= self.today_sets[s].active_ases
            utilized.append(self.today_sets[s].utilized)
        for s in self.first_day_sets:
            day_one_bw += self.first_day_sets[s].bandwidth
            day_one_active |= self.first_day_sets[s].active_ases

        for s in self.yesterday_sets:
            yesterday_bw += self.yesterday_sets[s].bandwidth
            yesterday_active |= self.yesterday_sets[s].active_ases

        mytmp = []
        for s in self.today_sets:
            mytmp.extend([s_.id for s_ in self.today_sets[s].subsets])
        mytmp = [i.split(classes.DELIMIT)[1] for i in mytmp]
        today_ssets = Set(mytmp)

        mytmp = []
        for s in self.yesterday_sets:
            mytmp.extend([s_.id for s_ in self.yesterday_sets[s].subsets])
        mytmp = [i.split(classes.DELIMIT)[1] for i in mytmp]
        yesterday_ssets = Set(mytmp)


        today_quantum = self.today_quantum
        yesterday_qunatum = self.yesterday_quantum

        today_sets =Set(today_sets)
        yesterday_sets = Set(yesterday_sets)










        adv_bw = 0.0
        adv_num = 0
        adv_asn = Set([])
        for ad in self.relays:
            if self.relays[ad]["adversary"] == 1:
                adv_num += 1
                adv_bw += self.relays[ad]["bandwidth"]
                adv_asn |= Set([self.relays[ad]["asn"]])
        quanta_change = len(self.yesterday_quantum) - len(self.today_quantum & self.yesterday_quantum)
        change_sets = len(self.yesterday_sets.keys()) - len(
            Set(self.yesterday_sets.keys()) & Set(self.today_sets.keys()))

        print(
            '\nIn:{0}:total BW:{1}\tASes:{2}\tDIFF FRM YEST:{3} \tDIFF FRM DAY1:{4}\tNEVER SEEN ASes:{5}\tSets:{6}\tQUA:{7}\tCR:{8}\tADV_NUM:{9}\tADV_BW:{10}\tCHNG_QU:{11}\tCHNG_SETS:{12}\tJ-CR:{13}\tS-CR:{14}\tJ-MEDBW:{15}\tS-MEDBW:{16}\tADV-ASN:{17}\tSETS:{18}\tSSETS:{19}\tQUNTA:{20}\tDSETS1:{21}\tDSSETS1:{22}\tDQUNTA1:{23}\t\tDSETS2:{24}\tDSSETS2:{25}\tDQUNTA2:{26}\t\tDSETS3:{27}\tDSSETS3:{28}\tDQUNTA3:{29}\tJSETS:{30}\tSINGLEBW:{31}\tUChngQ:{32}\tUChngS:{33}\tUChngSS:{34}'.format(
                self.date, int(today_bw), len(today_active), len(today_active - yesterday_active),
                len(today_active - day_one_active), len(today_active - self.never_seen_ases), len(self.today_sets),
                self.quantum_numbers, self.compromise_rate, adv_num, adv_bw, quanta_change, change_sets,
                self.jamies_users_compromised_rate, self.single_guard_users_compromised_rate, self.jamies_median_bw,
                self.single_guard_median_bw, len(adv_asn),
                len(today_sets),len(today_ssets),len(today_quantum),
                len(today_sets -yesterday_sets),len(today_ssets - yesterday_ssets),len(today_quantum - yesterday_qunatum),
                len(yesterday_sets - today_sets),len(yesterday_ssets - today_ssets), len(yesterday_qunatum - today_quantum),
                len(yesterday_sets) - len(today_sets),len(yesterday_ssets) - len(today_ssets), len(yesterday_qunatum) - len(today_quantum),self.number_jamies_sets,self.relays_bws, self.user_change_quanta,self.user_change_sset,self.user_change_set)
        )

        self.never_seen_ases |= today_active

        today_bw_list = []
        today_ases_list = []
        today_guards = []
        today_bw_set_list = []
        for s in self.today_sets:
            today_bw_list.append(self.today_sets[s].bandwidth)
            # today_bw_set_list.extend([q.bandwidth for s_ in self.today_sets[s].subsets for q in s_.quantum])
            today_bw_set_list.extend([s_.bandwidth for s_ in self.today_sets[s].subsets])
            today_ases_list.append(len(self.today_sets[s].ases))
            today_guards.append(len(self.today_sets[s].guards))



        print(
            "Statistics:\n\tBW:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}".format(
                numpy.percentile(today_bw_list, 10), numpy.percentile(today_bw_list, 25),
                numpy.percentile(today_bw_list, 50), numpy.percentile(today_bw_list, 75),
                numpy.percentile(today_bw_list, 90), min(today_bw_list), max(today_bw_list),numpy.mean(today_bw_list)))
        print("\tBWSSETS:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}".format(
            numpy.percentile(today_bw_set_list, 10), numpy.percentile(today_bw_set_list, 25),
            numpy.percentile(today_bw_set_list, 50), numpy.percentile(today_bw_set_list, 75),
            numpy.percentile(today_bw_set_list, 90), min(today_bw_set_list), max(today_bw_set_list),numpy.mean(today_bw_set_list)))
        print("\tGuards:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}".format(
            numpy.percentile(today_guards, 10), numpy.percentile(today_guards, 25), numpy.percentile(today_guards, 50),
            numpy.percentile(today_guards, 75), numpy.percentile(today_guards, 90), min(today_guards),
            max(today_guards),numpy.mean(today_guards)))
        print("\tASes:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}".format(
            numpy.percentile(today_ases_list, 10), numpy.percentile(today_ases_list, 25),
            numpy.percentile(today_ases_list, 50), numpy.percentile(today_ases_list, 75),
            numpy.percentile(today_ases_list, 90), min(today_ases_list), max(today_ases_list),numpy.mean(today_ases_list)))
        print("\tUSE:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}".format(
            numpy.percentile(utilized, 10), numpy.percentile(utilized, 25), numpy.percentile(utilized, 50),
            numpy.percentile(utilized, 75), numpy.percentile(utilized, 90), min(utilized), max(utilized),numpy.mean(utilized)))
        '''
        print("\tQBW:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}".format(
            numpy.percentile(quantum_bw, 10), numpy.percentile(quantum_bw, 25), numpy.percentile(quantum_bw, 50),
            numpy.percentile(quantum_bw, 75), numpy.percentile(quantum_bw, 90), min(quantum_bw), max(quantum_bw),numpy.mean(quantum_bw)))
        '''
        file_name = "log-f-{0}-a-{1}-u-{2}-m-{3}-ct-{4}-dt-{5}-i-{6}.new.log".format(self.adv_bw_fraction,
                                                                                     self.ADVERSARY_TYPE,
                                                                                     self.adv_num, self.MINIMUM_SETS,
                                                                                     self.CREATE_THRESHOLD,
                                                                                     self.DELETE_THRESHOLD,
                                                                                     self.interations)
        log_file = open(file_name,'a')
        log_file.write(
            'In:{0}:total BW:{1}\tASes:{2}\tDIFF FRM YEST:{3} \tDIFF FRM DAY1:{4}\tNEVER SEEN ASes:{5}\tSets:{6}\tSSubs:{7}\tCR:{8}\tADV_NUM:{9}\tADV_BW:{10}\tCHNG_QU:{11}\tCHNG_SETS:{12}\tJ-CR:{13}\tS-CR:{14}\tJ-MEDBW:{15}\tS-MEDBW:{16}\tADV-ASN:{17}\tSETS:{18}\tSSETS:{19}\tQUNTA:{20}\tDSETS1:{21}\tDSSETS1:{22}\tDQUNTA1:{23}\t\tDSETS2:{24}\tDSSETS2:{25}\tDQUNTA2:{26}\t\tDSETS3:{27}\tDSSETS3:{28}\tDQUNTA3:{29}\tJSETS:{30}\tSINGLEBW:{31}\tUChngQ:{32}\tUChngS:{33}\tUChngSS:{34}:\n'.format(
                self.date, int(today_bw), len(today_active), len(today_active - yesterday_active),
                len(today_active - day_one_active), len(today_active - self.never_seen_ases), len(self.today_sets),
                self.quantum_numbers, self.compromise_rate, adv_num, adv_bw, quanta_change, change_sets,
                self.jamies_users_compromised_rate, self.single_guard_users_compromised_rate, self.jamies_median_bw,
                self.single_guard_median_bw, len(adv_asn),
                len(today_sets),len(today_ssets),len(today_quantum),
                len(today_sets -yesterday_sets),len(today_ssets - yesterday_ssets),len(today_quantum - yesterday_qunatum),
                len(yesterday_sets - today_sets),len(yesterday_ssets - today_ssets), len(yesterday_qunatum - today_quantum),
                len(yesterday_sets) - len(today_sets),len(yesterday_ssets) - len(today_ssets), len(yesterday_qunatum) - len(today_quantum),self.number_jamies_sets,self.relays_bws,self.user_change_quanta,self.user_change_sset,self.user_change_set)
        )

        log_file.write(
            "Statistics:\tBW:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}:\n".format(
                numpy.percentile(today_bw_list, 10), numpy.percentile(today_bw_list, 25),
                numpy.percentile(today_bw_list, 50), numpy.percentile(today_bw_list, 75),
                numpy.percentile(today_bw_list, 90), min(today_bw_list), max(today_bw_list),numpy.mean(today_bw_list)))
        log_file.write("BWSSETS:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}:\n".format(
            numpy.percentile(today_bw_set_list, 10), numpy.percentile(today_bw_set_list, 25),
            numpy.percentile(today_bw_set_list, 50), numpy.percentile(today_bw_set_list, 75),
            numpy.percentile(today_bw_set_list, 90), min(today_bw_set_list), max(today_bw_set_list),numpy.mean(today_bw_set_list)))
        log_file.write("Guards:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}:\n".format(
            numpy.percentile(today_guards, 10), numpy.percentile(today_guards, 25), numpy.percentile(today_guards, 50),
            numpy.percentile(today_guards, 75), numpy.percentile(today_guards, 90), min(today_guards),
            max(today_guards),numpy.mean(today_guards)))
        log_file.write("ASes:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}:\n".format(
            numpy.percentile(today_ases_list, 10), numpy.percentile(today_ases_list, 25),
            numpy.percentile(today_ases_list, 50), numpy.percentile(today_ases_list, 75),
            numpy.percentile(today_ases_list, 90), min(today_ases_list), max(today_ases_list),numpy.mean(today_ases_list)))
        log_file.write("USE:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}:\n".format(
            numpy.percentile(utilized, 10), numpy.percentile(utilized, 25), numpy.percentile(utilized, 50),
            numpy.percentile(utilized, 75), numpy.percentile(utilized, 90), min(utilized), max(utilized),numpy.mean(utilized)))

        today_bw_list = []
        today_ases_list = []
        today_guards = []
        today_bw_set_list = []
        for s in self.today_sets:
            today_bw_list.append(self.today_sets[s].bandwidth)
            today_bw_set_list.extend([q.bandwidth for s_ in self.today_sets[s].subsets for q in s_.quantum])
            today_ases_list.extend([len(q.active_ases) for s_ in self.today_sets[s].subsets for q in s_.quantum])
            today_guards.extend([len(q.guards) for s_ in self.today_sets[s].subsets for q in s_.quantum])

        print("\tBWQUA:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}".format(
            numpy.percentile(today_bw_set_list, 10), numpy.percentile(today_bw_set_list, 25),
            numpy.percentile(today_bw_set_list, 50), numpy.percentile(today_bw_set_list, 75),
            numpy.percentile(today_bw_set_list, 90), min(today_bw_set_list), max(today_bw_set_list),numpy.mean(today_bw_set_list)))
        print("\tGuards-QUA:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}".format(
            numpy.percentile(today_guards, 10), numpy.percentile(today_guards, 25), numpy.percentile(today_guards, 50),
            numpy.percentile(today_guards, 75), numpy.percentile(today_guards, 90), min(today_guards),
            max(today_guards),numpy.mean(today_guards)))
        print("\tASes-QUA:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}".format(
            numpy.percentile(today_ases_list, 10), numpy.percentile(today_ases_list, 25),
            numpy.percentile(today_ases_list, 50), numpy.percentile(today_ases_list, 75),
            numpy.percentile(today_ases_list, 90), min(today_ases_list), max(today_ases_list),numpy.mean(today_ases_list)))

        log_file.write("BWQUA:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}:\n".format(
            numpy.percentile(today_bw_set_list, 10), numpy.percentile(today_bw_set_list, 25),
            numpy.percentile(today_bw_set_list, 50), numpy.percentile(today_bw_set_list, 75),
            numpy.percentile(today_bw_set_list, 90), min(today_bw_set_list), max(today_bw_set_list),numpy.mean(today_bw_set_list)))
        log_file.write("Guards-QUA:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}:\n".format(
            numpy.percentile(today_guards, 10), numpy.percentile(today_guards, 25), numpy.percentile(today_guards, 50),
            numpy.percentile(today_guards, 75), numpy.percentile(today_guards, 90), min(today_guards),
            max(today_guards),numpy.mean(today_guards)))
        log_file.write("ASes-QUA:\t10th:{0}\t25th:{1}\t50th:{2}\t75th:{3}\t90th:{4}\tMin:{5}\tMax:{6}\tAVG:{7}:\n".format(
            numpy.percentile(today_ases_list, 10), numpy.percentile(today_ases_list, 25),
            numpy.percentile(today_ases_list, 50), numpy.percentile(today_ases_list, 75),
            numpy.percentile(today_ases_list, 90), min(today_ases_list), max(today_ases_list),numpy.mean(today_ases_list)))

        log_file.close()

    def upload_dumped_data(self):
        print 'Reading customer cones from dataset'
        # self.parse_customer_cone()

        pr = open('../requirements/customers', 'r')
        self.customers = copy.copy(pickle.load(pr))
        pr.close()

        pr = open('../requirements/providers', 'r')
        self.providers = copy.copy(pickle.load(pr))
        pr.close()

        pr = open('../requirements/all_ases', 'r')
        self.all_ases = copy.copy(pickle.load(pr))
        pr.close()
        print 'done'


# print 'Start parsing the AS relationships...'
# asns = parse_as_relationships(os.path.join(classes.PATH_AS_DATASET, 'oix_relation_degree'))
# print 'AS relationships parsed, go for building the directed graph...'
# G = generate_directed_as_graph(asns)
# print 'Directed graph built.'
# customre_cone(asns)

parser = argparse.ArgumentParser()
parser.add_argument("-u", "--users", type=int, help="The number of users you would like to add", default=1)
parser.add_argument("-a", "--advType", type=int, help="The type of adversaries you would like to add", default=3)
parser.add_argument("-s", "--sets", type=int, help="The minimum number of sets", default=50)
parser.add_argument("-c", "--cthreshold", type=int, help="The minimum amount of bw to create sets or subsets",
                    default=40000)
parser.add_argument("-d", "--dthreshold", type=int, help="The minimum amount of bw to delete sets or subsets",
                    default=20000)
parser.add_argument("-n", "--adv_num", type=int, help="the number of adversaries we need to add to the network ",
                    default=0)
parser.add_argument("-f", "--adv_fraction", type=float,
                    help="the bw fraction of adversaries we need to add to the network ", default=0.0)
parser.add_argument("-p", "--processes", type=int, help="number of processes ", default=4)
parser.add_argument("-i", "--iterations", type=int, help="number of iterations ", default=1)
parser.add_argument("-m", "--multipath", type=int, help="number of multiple guards in multi-path", default=0) #Wladimir
#-u 500000 -a 7 -c 30000 -d 15000 -f 0.05 -i 15 -p 4
args = parser.parse_args()
users = args.users
adv = args.advType
min_sets = args.sets
cthreshold = args.cthreshold
dthreshold = args.dthreshold
adv_num = args.adv_num
adv_fraction = args.adv_fraction
classes.PROCESSES = args.processes
interations = args.iterations
multipath_ = args.multipath #Wladimir

for i in range(interations):
    print "iteration ", i
    proccess1 = as_set_proccess()
    proccess1.ADVERSARY_TYPE = adv
    proccess1.multipath = multipath_ #Wladimir
    proccess1.number_of_users = users
    proccess1.MINIMUM_SETS = min_sets
    proccess1.DELETE_THRESHOLD = dthreshold
    proccess1.CREATE_THRESHOLD = cthreshold
    proccess1.adv_bw_fraction = adv_fraction
    proccess1.adv_num = adv_num
    proccess1.interations = interations
    proccess1.upload_dumped_data()
    proccess1.daily_process()
