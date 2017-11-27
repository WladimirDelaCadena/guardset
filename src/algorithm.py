## This is the reference implementation of the Guard Set algorithm.
#  It takes a sequence of consesus docs and outputs the relations
#  between Guards, Guard Sets, User Sets, Users.


import pytest
import logging
import random
import bisect
import math
from collections import namedtuple, defaultdict
from copy import copy
from os import urandom
from binascii import hexlify
import operator
import os
import os.path
import re
from parseconsensus import parse_consensus1
import cProfile
from UGTree import UGTree, Branch, Leaf
import collections
from numpy import cumsum, sort, sum, searchsorted
from numpy.random import rand
import numpy as np
import classes
from sets import Set, ImmutableSet
#from pylab import hist,show,xticks
PATH_TO__SAVE = './files'
PATH_TO__DATA = '../requirements/consensuses-2015'  # './data-2013'
PATH_AS_DATASET = '../datasets'

def weighted_pick(weights,n_picks):
 """
  Weighted random selection
  returns n_picks random indexes.
  the chance to pick the index i
  is give by the weight weights[i].
 """
 t = cumsum(weights)
 s = sum(weights)
 return searchsorted(t,rand(n_picks)*s)


# Type definition
Guard = namedtuple('Guard', 'name, id, bw, bw_fraction')


# Structure that keeps track of Guard Sets
class GuardSet(object):

    def __init__(self, guards, backup, bounds, name):
        if __debug__:
            for g in guards:
                assert isinstance(g, tuple) and len(g) == 4

        self.guards = guards
        self.backup = backup
        self.BW_bounds = bounds

        self.name = name


    def get_quanta(self):
        return set([(g.name, g.id) for g in self.guards])


class GuardSetTree(object):
    """ An object to hold our tree of UGs and GSs,
    which makes it easy to add / delete or update GSs"""

    def __init__(self):
        ## The tree used to store
        self.tree = UGTree()
        ## A cache of the name of GSs for quick error checking
        self.names = set()

    def add_GSs(self, guard_sets):
        if __debug__:
            for gs in guard_sets:
                assert gs.name not in self.names

        for gs in guard_sets:
            pos = self.tree.new_naive_position()
            self.tree.insert_GS(pos, gs)
            self.names.add(gs.name)

    def update_GSs(self, guard_sets):
        if __debug__:
            for gs in guard_sets:
                assert gs.name in self.names

        leafs = self.get_Leafs()
        for gs in guard_sets:
            leafs[gs.name][1].content = gs


    def delete_GSs(self, guard_sets):
        if __debug__:
            for gs in guard_sets:
                assert gs.name in self.names

        for gs in guard_sets:
            leafs = self.get_Leafs()
            pos, _ = leafs[gs.name]
            self.tree.delete_GS(pos)

            self.names.remove(gs.name)

    def get_GSs(self):
        GS_list = self.tree.get_list()
        return [node.content for (pos, node) in GS_list]

    def get_Leafs(self):
        GS_list = self.tree.get_list()
        return { node.content.name : (pos, node) for (pos, node) in GS_list }



def get_all_gs_bandwidth(consensus, guard_sets, Threshold=40*1000):
    new_quanta = list_all_guard_quanta(consensus, Threshold)

    quanta_IDs = defaultdict(float)
    for q in new_quanta:
        quanta_IDs[(q.name, q.id)] = q.bw_fraction

    bw_gs_list = []
    for gs in guard_sets:
        new_bw = sum(quanta_IDs[g_id] for g_id in gs.get_quanta())
        bw_gs_list += [(gs, new_bw)]

    return bw_gs_list

def fix_guard_sets(c, guard_sets, fix_Threshold=20 * 1000, MAxThreshold = 40*1000):

    quanta = list_all_guard_quanta(c, Threshold=MAxThreshold)
    gs_bw = get_all_gs_bandwidth(c, guard_sets, Threshold=MAxThreshold)
    rest_of_quanta = filter_used_quanta(quanta, guard_sets)

    befor_guard_st = {}
    for gs in guard_sets:
        befor_guard_st[gs.name] = Set([g.name for g in gs.guards])

    broken_guard_sets = sorted([(bw, g, i) for i, (g, bw) in enumerate(gs_bw) if bw <= fix_Threshold])
    broken_id = [i for _,_,i in broken_guard_sets]
    fixed_id = []
    logging.debug("HD: FIX: the broken sets: %d", len(broken_guard_sets))
    rest_of_quanta = sorted(rest_of_quanta, key=lambda x: x.bw, reverse=True)
    logging.debug("HD: FIX: the leftovers: %d", len(rest_of_quanta))

    fixed_guard_sets = copy(guard_sets)
    for bw, gs, i in broken_guard_sets:
        [gmin, gmax] = gs.BW_bounds
        candidates = [q for q in rest_of_quanta if (gmax/float(2))<= q.bw <= gmax]
        logging.debug("HD: FIX: Repairing Set %s with %d candidates", gs.name, len(candidates))
        guards = copy(gs.guards)
        new_guards = []

        while bw < MAxThreshold and len(candidates) > 0:
             guards += [candidates[0]]
             bw += candidates[0].bw_fraction
             new_guards += [candidates[0]]
             logging.debug("HD: FIX: Repairing Set %s \t\t Guard %f added", gs.name, float(candidates[0].bw_fraction))
             del candidates[0]


        if bw > fix_Threshold:
            logging.debug("HD: FIX: Set %s repaired", gs.name)
            for g in new_guards:
                rest_of_quanta.remove(g)

            fixed_guard_sets[i] = GuardSet(guards, gs.backup, gs.BW_bounds, gs.name)
            fixed_id += [i]

    changes = 0
    i = 0
    for gs in fixed_guard_sets:
        if i in fixed_id:
            print ''
        tmp = Set([g.name for g in gs.guards])
        common = tmp - befor_guard_st[gs.name]
        if len(common) != 0:
            changes += 1
        i += 1
    logging.debug("BWdsign:REPAIR:%d:", changes)

    return fixed_guard_sets, (broken_id, fixed_id)


#added in min_allowance for becoming a guard

def list_all_guard_quanta(consensus, Threshold=40*1000, min_allowance=0):
    quanta = []
    for guard in sorted(consensus, key=lambda x: x["bandwidth"], reverse=True):
        if guard["bandwidth"] >= min_allowance:
            chunks = max(int(math.floor(float(guard["bandwidth"]) / Threshold)), 1)
            for Q in range(chunks):
                quanta += [(guard["ip"], Q, float(guard["bandwidth"]), float(guard["bandwidth"]) / chunks)]
    return map(Guard._make, quanta)

def filter_used_quanta(quanta, guard_sets):
    all_used_quanta = set()
    for gs in guard_sets:
        all_used_quanta |= gs.get_quanta()

    return [q for q in quanta if (q[0], q[1]) not in all_used_quanta]

def all_consensuses():
    consensuses = sorted(os.listdir(PATH_TO__DATA))
    for file_name in consensuses:
        if "consensus" not in file_name or '2015' not in file_name:
            continue

        full_name = os.path.join(PATH_TO__DATA, file_name)
        data = file(full_name).read()
        name = re.sub('-00-00-00-consensus', '', file_name)
        yield name, parse_consensus1(data)["relays"]

def guard_churn():
    prev_quanta = []
    date = []
    added_guards = []
    deleted_guards = []
    number_guards = []
    for name, c in all_consensuses():
        quanta = list_all_guard_quanta(c)
        added = len(available_guards(quanta, prev_quanta))
        removed = len(available_guards(prev_quanta, quanta))
        #print "%s +%s -%s" % (name, added, removed)
        date.append(name)
        added_guards.append(added)
        deleted_guards.append(removed)
        number_guards.append(len(quanta))
        prev_quanta = quanta
    return date, added_guards, deleted_guards, number_guards

def available_guards(current_quanta, quanta_in_guard_sets):
    f = lambda x: (x[0], x[1])

    quanta = set(map(f, current_quanta))
    quanta -= set(map(f, quanta_in_guard_sets))
    return quanta


def new_guard_sets(available_quanta, Threshold=40*1000, min_f = 0.0, randomized=False):
    # min_f the fractions of the bandwidth to be in the same set
    # as another guard


    quanta = sorted(available_quanta, key=lambda x: x.bw_fraction, reverse=True)
    all_gs = []

    while len(quanta) > 0:
        top_bw = quanta[0].bw
        min_bw = min_f * top_bw
        candidates = [q for q in quanta if q.bw >= min_bw]

        if randomized:
            random.shuffle(candidates)

        gs = []
        gs_bw = 0
        while gs_bw < Threshold and len(candidates) > 0:
            gs += [candidates[0]]
            gs_bw += candidates[0].bw_fraction
            del candidates[0]

        backup_bw = 0.0
        backup = []
        gs_node_set = set([g.name for g in gs])
        while backup_bw < Threshold and len(candidates) > 0:
            if candidates[0].name in gs_node_set:
                del candidates[0]
                continue
            backup += [candidates[0]]
            backup_bw += candidates[0].bw_fraction
            del candidates[0]

        name = hexlify(urandom(16))
        if gs_bw >= Threshold:
            gs_obj = GuardSet(gs, backup, [min_bw, top_bw], name)
            all_gs += [gs_obj]
            for g in gs:
                quanta.remove(g)
        else:
            #print "Last GS Bandwidth: ", gs_bw
            #for g in gs:
            #    print g
            #print
            break

    return all_gs, quanta

def new_guard_sets_alt(available_quanta, lim=40*1000):
    guardsets = []
    temp_size = 0
    temp_set = []
    quanta = sorted(available_quanta, key=lambda x: x[2], reverse=True)
    for i in quanta:
        if i[2] > lim:
            num = int(i[2] / lim)
            for _ in range(num):
              guardsets.append([i])
        else:
            temp_size += i[2]
            temp_set.append(i)
            if temp_size > lim:
                guardsets.append(temp_set)
                temp_size = 0
                temp_set = []
    if temp_set != []:
        guardsets[-1].extend(temp_set)

    print guardsets

def total_guard_set_bw(guard_sets):

    sum_bw = 0
    for x in guard_sets:
        for i in x.__dict__["guards"]:
            sum_bw += i.bw_fraction
    return sum_bw

def average_guard_set_bw(guard_sets):
    temp = []
    for x in guard_sets:
        sum_bw = 0
        for i in x.__dict__["guards"]:
            sum_bw = sum_bw + i.bw_fraction
        temp.append(sum_bw)
    return sum(temp)/len(guard_sets)



def my_guard_set_bw(guard_sets):
    temp = []
    for x in guard_sets:
        sum_bw = 0
        for i in x.__dict__["guards"]:
            sum_bw = sum_bw + i.bw_fraction
        temp.append(sum_bw)
    return temp


def median_guard_set_bw(guard_sets):
    temp = []
    for x in guard_sets:
        sum_bw = 0
        for i in x.__dict__["guards"]:
            sum_bw = sum_bw + i.bw_fraction
        temp.append(sum_bw)
    return [np.percentile(temp,10),np.percentile(temp,25),np.percentile(temp,50),np.percentile(temp,75),np.percentile(temp,90),min(temp),max(temp),np.median(temp)]

def test_average_gs_bw():
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())["relays"]
    quanta = list_all_guard_quanta(c)

    guard_sets, spare_quanta = new_guard_sets(quanta)
    print average_guard_set_bw(guard_sets)

def guard_set_bw(guard_set):
    bw = 0
    for i in guard_set.__dict__["guards"]:
        bw += i.bw_fraction
    return bw

def test_gs_bw():
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())["relays"]
    quanta = list_all_guard_quanta(c)

    guard_sets, spare_quanta = new_guard_sets(quanta)

    x = random.choice(guard_sets)
    print guard_set_bw(x)
    print
    for g in x.guards:
        print g



def user_dist(c):
    #for name, c in all_consensuses():
    gsTree = GuardSetTree()
    quanta = list_all_guard_quanta(c)
    guard_sets = gsTree.get_GSs()
    ## Fix them, if possible!
    fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
    assert len(fixed_guard_sets) == len(guard_sets)
    for gs in fixed_guard_sets:
        assert isinstance(gs, GuardSet)
    guard_sets = fixed_guard_sets
    gsTree.update_GSs(guard_sets)
    # # Detect the weak ones, kill them off
    gs_bw = get_all_gs_bandwidth(c, guard_sets)
    Kill_threshold = 20000
    killed_guard_sets = [g for g, bw in gs_bw if bw < Kill_threshold]
    num_killed = len(killed_guard_sets)
    gsTree.delete_GSs(killed_guard_sets)
    ## Make new GSs
    guard_sets = gsTree.get_GSs()
    rest_of_quanta = filter_used_quanta(quanta, guard_sets)
    min_f = 0.0
    randomized=False
    new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)
    gsTree.add_GSs(new_sets)
    guard_sets = gsTree.get_GSs()
    leaves = gsTree.get_Leafs()
    position = []

    for keys, values in leaves.items():
        pos_len = len(values[0])
        pos = values[0]
        position.append((keys, pos, pos_len))

    sort_pos = sorted(position, key=lambda x: x[2])

    weights = []
    weights_adj = []

    i = sort_pos[-1][2]
    for item in sort_pos:
        weights.append((item[0], float(i)/item[2]))

    m = 1
    j = -1
    for i, x in enumerate(weights):
        if (weights[j+1][1] - weights[j][1]) < 0:
            weights_adj.append((x[0], m))
            m = m/float(2)
            j+=1
        else:
            weights_adj.append((x[0], m))
            j+=1

    # picking 10000 times
    #picked_list = weighted_pick(zip(*weights_adj)[1],1000000)

    sumOfWeights = sum(zip(*weights_adj)[1])
    probabilities = [(i/float(sumOfWeights)) for i in zip(*weights_adj)[1]]
    user_fractions = zip(zip(*weights_adj)[0], probabilities)
    d = dict(user_fractions)

    # plotting the histogram
    #hist(picked_list,bins=len(zip(*weights_adj)[1]),normed=1,alpha=.8,color='red')
    #show()

    assert len(d) == len(weights_adj) == len(weights) == len(sort_pos)

    return d


def update_user_dist(c, guard_sets):
    #tracks the fraction of users at each gs at each consensus
    pass

#########################################
### ------------ TESTS ------------------

def test_delete_GS():
    tree = UGTree()
    for i in range(10):
        p = tree.new_naive_position()
        tree.insert_GS(p, "GS%i" % i)
    assert tree.count() == 10

    print("old Tree")
    print(tree.to_string())

    node_list = tree.get_list()
    for (pos, node) in node_list:
        deleted = tree.delete_GS(pos)
        assert node.content == deleted.content

    print("New Tree")
    print(tree.to_string())

    with pytest.raises(Exception) as exinfo:
        tree.delete_GS(pos)

def test_insert_GS():
    tree = UGTree()
    p = tree.new_naive_position()
    tree.insert_GS(p, "Hello")
    assert tree.count() == 1

    for i in range(100):
        p = tree.new_naive_position()
        tree.insert_GS(p, "GS%i" % i)
        print tree

    assert tree.count() == 101

    #print(tree.to_string())
    #assert False

def test_naive_position():
    tree = UGTree()
    positions = tree.new_naive_position()
    assert len(positions) == 64


def test_consensus_sequence():
    for name, c in all_consensuses():
        assert len(c) > 0
        print name


def test_consensus_sequence():
    prev_quanta = []
    date = []
    added_guards = []
    deleted_guards = []
    for name, c in all_consensuses():
        quanta = list_all_guard_quanta(c)
        added = len(available_guards(quanta, prev_quanta))
        removed = len(available_guards(prev_quanta, quanta))
        print "%s +%s -%s" % (name, added, removed)
        date.append(name)
        added_guards.append(added)
        deleted_guards.append(removed)
        prev_quanta = quanta



def test_consensus_algo1():
    prev_quanta = []
    guard_sets = []
    date = []
    new_gs = []
    deleted_gs = []
    gs_total = []
    broken_gs = []
    fixed_gs = []

    print
    for name, c in all_consensuses():
        quanta = list_all_guard_quanta(c)

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        num_killed = len(guard_sets)
        guard_sets = [g for g, bw in gs_bw if bw > Kill_threshold]
        num_killed -= len(guard_sets)

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)


        guard_sets += new_sets


        new_gs_ids = []
        for i, gs in enumerate(new_sets):
            if gs.name not in new_gs_ids:
                new_gs_ids.append(gs.name)

        date.append(name)
        new_gs.append(len(new_sets))
        deleted_gs.append(num_killed)
        gs_total.append(len(guard_sets))
        broken_gs.append(len(broken_id))
        fixed_gs.append(len(fixed_id))

        #print "%s:\t+%s\t-%s\t%s\tBroken %s\tFixed: %s" % (name, len(new_sets), num_killed, len(guard_sets), len(broken_id), len(fixed_id))
        #print
        #print "New guard set ID's:", new_gs_ids
    #print sum(new_gs), sum(deleted_gs)
    return date, new_gs, deleted_gs, gs_total, broken_gs, fixed_gs


def test_can_read_consensus():
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())
    assert isinstance(c, dict)
    assert "relays" in c and (len(c) == 1)


def test_can_read_quanta():
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())["relays"]
    quanta = list_all_guard_quanta(c)

    for x in quanta:
        print(x)


def test_make_guard_sets_rand():
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())["relays"]
    quanta = list_all_guard_quanta(c)

    guard_sets, spare_quanta = new_guard_sets(quanta)


    for i, gs in enumerate(guard_sets):
        print
        print "------------------"
        print "Guard set number:", i
        print #gs.__dict__                            #shows properties of guard sets
        print "Guard set id:", gs.name
        print "Guard set bw bounds:", gs.BW_bounds
        print
        for g in gs.guards:
            print g



def test_filter():
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())["relays"]
    quanta = list_all_guard_quanta(c)
    guard_sets, spare_quanta = new_guard_sets(quanta)

    remaining = filter_used_quanta(quanta, guard_sets)
    assert sum(map(lambda x: x[-1], remaining)) < 40000


def test_get_bw():
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())["relays"]
    quanta = list_all_guard_quanta(c)
    guard_sets, spare_quanta = new_guard_sets(quanta)

    gs_bw = get_all_gs_bandwidth(c, guard_sets)

    for name, c in all_consensuses():

        quanta = list_all_guard_quanta(c)

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        num_killed = len(guard_sets)
        guard_sets = [g for g, bw in gs_bw if bw > Kill_threshold]
        num_killed -= len(guard_sets)

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)
        guard_sets += new_sets
        print
        print "--------"
        print

        for i, (gs, bw) in enumerate(gs_bw):
            print "%s (bandwidth=%s)" % (i, bw)
            for g in gs.guards:
                print g


def test_make_guard_sets_alt():
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())["relays"]
    quanta = list_all_guard_quanta(c)
    guard_sets= new_guard_sets_alt(quanta)


## interestingly avg gs bw is around 50MB/s when threshold is 40

def test_guard_set_bw():
    prev_quanta = []
    guard_sets = []
    spare_list = []
    total_bw_list = []
    average_gs_bw = []
    dates = []
    gsTree = GuardSetTree()

    for name, c in all_consensuses():
        dates.append(name)
        quanta = list_all_guard_quanta(c)
        guard_sets = gsTree.get_GSs()

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        num_killed = len(guard_sets)
        guard_sets = [g for g, bw in gs_bw if bw > Kill_threshold]
        num_killed -= len(guard_sets)

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)


        guard_sets += new_sets

        total_gs_bw = total_guard_set_bw(guard_sets)
        total_bw_list.append(total_gs_bw)
        average_gs_bw.append(average_guard_set_bw(guard_sets))

        spare_bw = 0
        for x in spare_quanta:
            spare_bw += x.bw_fraction
        spare_list.append(spare_bw)

        #print "%s:\t\tSpare bw %s\t\tTotal guard bw: %s\t\tAverage gs bw: %s" % (name, spare_bw, total_gs_bw, average_guard_set_bw(guard_sets))

        #print name, average_guard_set_bw(guard_sets), total_gs_bw, spare_bw
    assert len(spare_list) == len(total_bw_list) == len(dates)
    #print dates
    #print "---------------"
    #print spare_list
    #print "---------------"
    #print total_bw_list
    #print "---------------"
    #print average_gs_bw
    return dates, spare_list, total_bw_list, average_gs_bw


def test_consensus_algo2():
    prev_quanta = []
    gsTree = GuardSetTree()
    date_gs_map = {}
    print
    for name, c in all_consensuses():
        quanta = list_all_guard_quanta(c)

        guard_sets = gsTree.get_GSs()

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        gsTree.update_GSs(guard_sets)

        # # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        killed_guard_sets = [g for g, bw in gs_bw if bw < Kill_threshold]
        num_killed = len(killed_guard_sets)

        gsTree.delete_GSs(killed_guard_sets)

        ## Make new GSs
        guard_sets = gsTree.get_GSs()

        for x in guard_sets:
            date_gs_map.setdefault(x.__dict__["name"],[]).append(name)

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)
        gsTree.add_GSs(new_sets)

        guard_sets = gsTree.get_GSs()

        spare_bw = 0
        for x in spare_quanta:
            spare_bw += x.bw_fraction

        print "%s:\t+%s\t-%s\t%s\tBroken %s\tFixed: %s\tSpare bw: %s" % (name, len(new_sets), num_killed, len(guard_sets), len(broken_id), len(fixed_id), spare_bw)

    #print date_gs_map
    #print len(date_gs_map)

def sample_Adv(consensus, Adv_bw, include_guards=[]):

    c = consensus
    #quanta = list_all_guard_quanta(c)
    #guard_sets, spare_quanta = new_guard_sets(quanta)

    Adv_relays = {}
    Current_bw = 0

    existing = set([])
    Current_bw = sum([], 0)



    if Adv_bw == 0.0:
        x = copy(random.choice(c.values()))
        x["ip"] = str(random.randint(0,255)) + "." + str(random.randint(0,255)) + "." + str(random.randint(0,255)) + "." + str(random.randint(0,255))
        Adv_relays[x['ip']]= x

    else:
        for _ in range(1000):
            x = copy(random.choice(c.values()))

            if x['bandwidth'] + Current_bw <= Adv_bw and x['ip'] not in Adv_relays:
                x["ip"] = str(random.randint(0,255)) + "." + str(random.randint(0,255)) + "." + str(random.randint(0,255)) + "." + str(random.randint(0,255))
                Adv_relays[x['ip']]= x
                Current_bw += x['bandwidth']


    return Adv_relays


def test_sample_Adv():
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())["relays"]
    print sample_Adv(c, 80000)


def test_algo3():
    prev_quanta = []
    gsTree = GuardSetTree()
    gs_dict_verb = {} #verbose
    gs_dict = {} #concise
    gs_bw_dict = {}
    gs_bw_frac = {}
    gs_user_dist = {}
    date_gs_map = {}

    #make this for every beginning of month of consensus not just 01/01/13
    c = parse_consensus1(file(r"../data/daily/2013-01-01-00-00-00-consensus").read())["relays"]

    total_guard_bw = sum(entry['bandwidth'] for entry in c)

    adv_guards = sample_Adv(c, 0.05*total_guard_bw, include_guards=[])


    corrupted_gs = dict((g,[]) for g in adv_guards)

    print
    for name, c in all_consensuses():

        quanta = list_all_guard_quanta(c)
        guard_sets = gsTree.get_GSs()

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        gsTree.update_GSs(guard_sets)

        # # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        killed_guard_sets = [g for g, bw in gs_bw if bw < Kill_threshold]
        num_killed = len(killed_guard_sets)

        gsTree.delete_GSs(killed_guard_sets)


        ## Make new GSs
        guard_sets = gsTree.get_GSs()

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)
        gsTree.add_GSs(new_sets)

        guard_sets = gsTree.get_GSs()
        leaves = gsTree.get_Leafs()

        #--------------

        for k, v in corrupted_gs.items():
            a = [x.__dict__["name"] for x in guard_sets if k in x.__dict__["guards"]]
            corrupted_gs[k].extend(a)

        #---------------

        position = []

        for keys, values in leaves.items():
            pos_len = len(values[0])
            pos = values[0]
            position.append((keys, pos, pos_len))

        sort_pos = sorted(position, key=lambda x: x[2])

        weights = []
        weights_adj = []

        i = sort_pos[-1][2]
        for item in sort_pos:
            weights.append((item[0], float(i)/item[2]))

        m = 1
        j = -1
        for i, x in enumerate(weights):
            if (weights[j+1][1] - weights[j][1]) < 0:
                weights_adj.append((x[0], m))
                m = m/float(2)
                j+=1
            else:
                weights_adj.append((x[0], m))
                j+=1

        # picking 10000 times
        #picked_list = weighted_pick(zip(*weights_adj)[1],1000000)

        sumOfWeights = sum(zip(*weights_adj)[1])
        probabilities = [(i/float(sumOfWeights)) for i in zip(*weights_adj)[1]]
        user_fractions = zip(zip(*weights_adj)[0], probabilities)
        d = dict(user_fractions)

        # plotting the histogram
        #hist(picked_list,bins=len(zip(*weights_adj)[1]),normed=1,alpha=.8,color='red')
        #show()

        assert len(d) == len(weights_adj) == len(weights) == len(sort_pos)

        for keys, values in d.items():
            gs_user_dist.setdefault(keys,[]).append(values)

        #-----------

        #temp = []
        #for keys,values in leaves.items():
        #    temp.append((keys, values[0]))
        #b = sorted(temp, lambda x,y: 1 if len(x[1])>len(y[1]) else -1 if len(x[1])<len(y[1]) else 0)
        #print "------------------"
        #for x in b:
        #    print "Guard set: %s\tPosition: %s" % (x[0], x[1])

        for keys, values in leaves.items():
            gs_dict_verb.setdefault(keys,[]).append(values[0])

        for x in guard_sets:
            gs_bw_dict.setdefault(x.__dict__["name"],[]).append(guard_set_bw(x))


        #for x in guard_sets:
        #    gs_bw_frac.setdefault(x.__dict__["name"],[]).append(guard_set_bw(x) / total_guard_set_bw(guard_sets))

        for x in guard_sets:
            date_gs_map.setdefault(x.__dict__["name"],[]).append(name)

    for keys, values in gs_dict_verb.items():
        gs_dict[keys] = {
        'Deepest Position' : max(values,key=len),
        'Shallowest Position' : min(values,key=len),
        }
        #print "Guard set: %s\tDeepest Position: %s\t\tShallowest Position: %s" % (keys, max(values,key=len), min(values,key=len))

    assert len(gs_dict) == len(gs_bw_dict)

    ds = [gs_bw_dict, gs_dict_verb]
    gs_bw_pos = {}
    for k in gs_bw_dict.iterkeys():
        gs_bw_pos[k] = tuple(gs_bw_pos[k] for gs_bw_pos in ds)
    for keys, values in gs_bw_pos.items():
        assert len(values[0]) == len(values[1])
    #print gs_bw_pos

    gs_bw_dict_verb = {}
    for keys, values in gs_bw_dict.items():
        gs_bw_dict_verb[keys] = {
        'Bandwidth' : values,
        }

    gs_user_dist_verb = {}
    for keys, values in gs_user_dist.items():
        gs_user_dist_verb[keys] = {
        'Fraction of users' : values,
        }

    #gs_bw_frac_verb = {}
    #for keys, values in gs_bw_frac.items():
    #    gs_bw_frac_verb[keys] = {
    #    'Fraction of guard set bw' : values,
    #    }

    gs_dates = {}
    for keys, values in date_gs_map.items():
        gs_dates[keys] = {
        'Dates' : values,
        }

    assert len(gs_bw_dict_verb) == len(gs_dict) == len(gs_user_dist_verb) == len(gs_dates)
    master = [gs_bw_dict_verb, gs_dict, gs_user_dist_verb, gs_dates]
    d = {}
    for k in gs_bw_dict_verb.iterkeys():
        d[k] = tuple(d[k] for d in master)

    unique_adv_gs = {}
    for k, v in corrupted_gs.items():
        unique_adv_gs[k] = list(set(v))


    comp_gs_dates_fract_users = []
    for keys, values in d.items():
        for a, b in corrupted_gs.items():
            if keys in b:
                comp_gs_dates_fract_users.append((values[3]["Dates"], values[2]["Fraction of users"]))


    # this gives a dictionary of dates with compromised users
    dict1 = {}
    for item in comp_gs_dates_fract_users:
        for i, d in enumerate(item[0]):
            dict1.setdefault(d,[]).append(item[1][i])

    # sum the values for each key(date) to get total fraction of compromised users at each date
    dict2 = {}
    for k, v in dict1.items():
        dict2[k] = [sum(v)]
    print dict2





def test_algo3_x_times():
    c=0
    dict1 = {}

    for _ in range(1000):
        print "%d" %c
        c+=1
        dict2 = test_algo3()

        for k, v in dict2.items():
            dict1.setdefault(k, []).extend(v)


    return dict1





def test_algo4():
    prev_quanta = []
    gsTree = GuardSetTree()
    gs_dict_verb = {} #verbose
    gs_dict = {} #concise
    gs_bw_dict = {}
    gs_bw_frac = {}
    gs_user_dist = {}
    date_gs_map = {}
    print
    for name, c in all_consensuses():

        quanta = list_all_guard_quanta(c)
        guard_sets = gsTree.get_GSs()

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        gsTree.update_GSs(guard_sets)

        # # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        killed_guard_sets = [g for g, bw in gs_bw if bw < Kill_threshold]
        num_killed = len(killed_guard_sets)

        gsTree.delete_GSs(killed_guard_sets)


        ## Make new GSs
        guard_sets = gsTree.get_GSs()

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)
        gsTree.add_GSs(new_sets)

        guard_sets = gsTree.get_GSs()
        leaves = gsTree.get_Leafs()

        #--------------


        position = []

        for keys, values in leaves.items():
            pos_len = len(values[0])
            pos = values[0]
            position.append((keys, pos, pos_len))

        sort_pos = sorted(position, key=lambda x: x[2])

        weights = []
        weights_adj = []

        i = sort_pos[-1][2]
        for item in sort_pos:
            weights.append((item[0], float(i)/item[2]))

        m = 1
        j = -1
        for i, x in enumerate(weights):
            if (weights[j+1][1] - weights[j][1]) < 0:
                weights_adj.append((x[0], m))
                m = m/float(2)
                j+=1
            else:
                weights_adj.append((x[0], m))
                j+=1

        # picking 10000 times
        #picked_list = weighted_pick(zip(*weights_adj)[1],1000000)

        sumOfWeights = sum(zip(*weights_adj)[1])
        probabilities = [(i/float(sumOfWeights)) for i in zip(*weights_adj)[1]]
        user_fractions = zip(zip(*weights_adj)[0], probabilities)
        d = dict(user_fractions)

        # plotting the histogram
        #hist(picked_list,bins=len(zip(*weights_adj)[1]),normed=1,alpha=.8,color='red')
        #show()

        assert len(d) == len(weights_adj) == len(weights) == len(sort_pos)

        for keys, values in d.items():
            gs_user_dist.setdefault(keys,[]).append(values)

        #-----------

        #temp = []
        #for keys,values in leaves.items():
        #    temp.append((keys, values[0]))
        #b = sorted(temp, lambda x,y: 1 if len(x[1])>len(y[1]) else -1 if len(x[1])<len(y[1]) else 0)
        #print "------------------"
        #for x in b:
        #    print "Guard set: %s\tPosition: %s" % (x[0], x[1])

        for keys, values in leaves.items():
            gs_dict_verb.setdefault(keys,[]).append(values[0])

        for x in guard_sets:
            gs_bw_dict.setdefault(x.__dict__["name"],[]).append(guard_set_bw(x))


        for x in guard_sets:
            gs_bw_frac.setdefault(x.__dict__["name"],[]).append(guard_set_bw(x) / total_guard_set_bw(guard_sets))

        for x in guard_sets:
            date_gs_map.setdefault(x.__dict__["name"],[]).append(name)


    for keys, values in gs_dict_verb.items():
        gs_dict[keys] = {
        'Deepest Position' : max(values,key=len),
        'Shallowest Position' : min(values,key=len),
        }
        #print "Guard set: %s\tDeepest Position: %s\t\tShallowest Position: %s" % (keys, max(values,key=len), min(values,key=len))

    assert len(gs_dict) == len(gs_bw_dict)

    ds = [gs_bw_dict, gs_dict_verb]
    gs_bw_pos = {}
    for k in gs_bw_dict.iterkeys():
        gs_bw_pos[k] = tuple(gs_bw_pos[k] for gs_bw_pos in ds)
    for keys, values in gs_bw_pos.items():
        assert len(values[0]) == len(values[1])
    #print gs_bw_pos

    gs_bw_dict_verb = {}
    for keys, values in gs_bw_dict.items():
        gs_bw_dict_verb[keys] = {
        'Bandwidth' : values,
        }

    gs_user_dist_verb = {}
    for keys, values in gs_user_dist.items():
        gs_user_dist_verb[keys] = {
        'Fraction of users' : values,
        }

    gs_bw_frac_verb = {}
    for keys, values in gs_bw_frac.items():
        gs_bw_frac_verb[keys] = {
        'Fraction of guard set bw' : values,
        }

    gs_dates = {}
    for keys, values in date_gs_map.items():
        gs_dates[keys] = {
        'Dates' : values,
        }


    #print gs_user_dist
    assert len(gs_bw_dict_verb) == len(gs_dict) == len(gs_user_dist_verb) == len(gs_bw_frac_verb) == len(gs_dates)
    master = [gs_bw_dict_verb, gs_dict, gs_user_dist_verb, gs_bw_frac_verb, gs_dates]
    d = {}
    for k in gs_bw_dict_verb.iterkeys():
        d[k] = tuple(d[k] for d in master)

    return d



def test_single_adv():
    prev_quanta = []
    gsTree = GuardSetTree()
    gs_dict_verb = {} #verbose
    gs_dict = {} #concise
    gs_bw_dict = {}
    gs_bw_frac = {}
    gs_user_dist = {}
    date_gs_map = {}

    c = parse_consensus1(file(r"../consensus/all/2013-01-01-00-00-00-consensus").read())["relays"]
    quanta = list_all_guard_quanta(c)

    guard_sets, spare_quanta = new_guard_sets(quanta)

    x = random.choice(guard_sets)
    corrupt_guard = random.choice(x.__dict__["guards"])
    print "Corrupt guard:", corrupt_guard
    corrupted_gs = {corrupt_guard : []}


    print
    tt = 0
    for name, c in all_consensuses():
        tt += 1
        if tt == 10: break
        quanta = list_all_guard_quanta(c)
        guard_sets = gsTree.get_GSs()

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        gsTree.update_GSs(guard_sets)

        # # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        killed_guard_sets = [g for g, bw in gs_bw if bw < Kill_threshold]
        num_killed = len(killed_guard_sets)

        gsTree.delete_GSs(killed_guard_sets)


        ## Make new GSs
        guard_sets = gsTree.get_GSs()

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)
        gsTree.add_GSs(new_sets)

        guard_sets = gsTree.get_GSs()
        leaves = gsTree.get_Leafs()

        #--------------


        a = [x.__dict__["name"] for x in guard_sets if corrupt_guard in x.__dict__["guards"]]
        corrupted_gs[corrupt_guard].extend(a)

        #---------------

        position = []

        for keys, values in leaves.items():
            pos_len = len(values[0])
            pos = values[0]
            position.append((keys, pos, pos_len))

        sort_pos = sorted(position, key=lambda x: x[2])

        weights = []
        weights_adj = []

        i = sort_pos[-1][2]
        for item in sort_pos:
            weights.append((item[0], float(i)/item[2]))

        m = 1
        j = -1
        for i, x in enumerate(weights):
            if (weights[j+1][1] - weights[j][1]) < 0:
                weights_adj.append((x[0], m))
                m = m/float(2)
                j+=1
            else:
                weights_adj.append((x[0], m))
                j+=1

        # picking 10000 times
        #picked_list = weighted_pick(zip(*weights_adj)[1],1000000)

        sumOfWeights = sum(zip(*weights_adj)[1])
        probabilities = [(i/float(sumOfWeights)) for i in zip(*weights_adj)[1]]
        user_fractions = zip(zip(*weights_adj)[0], probabilities)
        d = dict(user_fractions)

        # plotting the histogram
        #hist(picked_list,bins=len(zip(*weights_adj)[1]),normed=1,alpha=.8,color='red')
        #show()

        assert len(d) == len(weights_adj) == len(weights) == len(sort_pos)

        for keys, values in d.items():
            gs_user_dist.setdefault(keys,[]).append(values)

        #-----------

        #temp = []
        #for keys,values in leaves.items():
        #    temp.append((keys, values[0]))
        #b = sorted(temp, lambda x,y: 1 if len(x[1])>len(y[1]) else -1 if len(x[1])<len(y[1]) else 0)
        #print "------------------"
        #for x in b:
        #    print "Guard set: %s\tPosition: %s" % (x[0], x[1])

        for keys, values in leaves.items():
            gs_dict_verb.setdefault(keys,[]).append(values[0])

        for x in guard_sets:
            gs_bw_dict.setdefault(x.__dict__["name"],[]).append(guard_set_bw(x))


        for x in guard_sets:
            date_gs_map.setdefault(x.__dict__["name"],[]).append(name)


    for keys, values in gs_dict_verb.items():
        gs_dict[keys] = {
        'Deepest Position' : max(values,key=len),
        'Shallowest Position' : min(values,key=len),
        }
        #print "Guard set: %s\tDeepest Position: %s\t\tShallowest Position: %s" % (keys, max(values,key=len), min(values,key=len))

    assert len(gs_dict) == len(gs_bw_dict)

    ds = [gs_bw_dict, gs_dict_verb]
    gs_bw_pos = {}
    for k in gs_bw_dict.iterkeys():
        gs_bw_pos[k] = tuple(gs_bw_pos[k] for gs_bw_pos in ds)
    for keys, values in gs_bw_pos.items():
        assert len(values[0]) == len(values[1])
    #print gs_bw_pos

    gs_bw_dict_verb = {}
    for keys, values in gs_bw_dict.items():
        gs_bw_dict_verb[keys] = {
        'Bandwidth' : values,
        }

    gs_user_dist_verb = {}
    for keys, values in gs_user_dist.items():
        gs_user_dist_verb[keys] = {
        'Fraction of users' : values,
        }

    gs_dates = {}
    for keys, values in date_gs_map.items():
        gs_dates[keys] = {
        'Dates' : values,
        }


    #print gs_user_dist
    assert len(gs_bw_dict_verb) == len(gs_dict) == len(gs_user_dist_verb) == len(gs_dates)
    master = [gs_bw_dict_verb, gs_dict, gs_user_dist_verb, gs_dates]
    d = {}
    for k in gs_bw_dict_verb.iterkeys():
        d[k] = tuple(d[k] for d in master)

    #print d
    corrupted_gs = {corrupt_guard : list(set(corrupted_gs[corrupt_guard]))}
    print corrupted_gs
    print "Number of guard sets corrupted: %s" % (len(corrupted_gs[corrupt_guard]))
    print "--------------"


    for keys, values in d.items():
        for a, b in corrupted_gs.items():
            if keys in b:
                print "Corrupted guard set:", keys, "-----", "Fraction of users corrupted: %s" % (values[2]["Fraction of users"])
                return values[3]["Dates"], values[2]["Fraction of users"]



def test_single_adv_x_times():
    c=0
    dict1 = {}
    for _ in range(100):
        print "%d" %c
        c+=1
        a, b = test_single_adv()
        for i, x in enumerate(a):
            dict1.setdefault(x, []).append(b[i])
    return dict1


def test_cdf():
    prev_quanta = []
    gsTree = GuardSetTree()
    gs_dict_verb = {} #verbose
    gs_dict = {} #concise
    gs_bw_dict = {}
    gs_bw_frac = {}
    gs_user_dist = {}
    date_gs_map = {}
    gs_guards = {}
    print
    for name, c in all_consensuses():

        quanta = list_all_guard_quanta(c)
        guard_sets = gsTree.get_GSs()

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        gsTree.update_GSs(guard_sets)

        # # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        killed_guard_sets = [g for g, bw in gs_bw if bw < Kill_threshold]
        num_killed = len(killed_guard_sets)

        gsTree.delete_GSs(killed_guard_sets)


        ## Make new GSs
        guard_sets = gsTree.get_GSs()

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)
        gsTree.add_GSs(new_sets)

        guard_sets = gsTree.get_GSs()
        leaves = gsTree.get_Leafs()

        #--------------


        position = []

        for keys, values in leaves.items():
            pos_len = len(values[0])
            pos = values[0]
            position.append((keys, pos, pos_len))

        sort_pos = sorted(position, key=lambda x: x[2])

        weights = []
        weights_adj = []

        i = sort_pos[-1][2]
        for item in sort_pos:
            weights.append((item[0], float(i)/item[2]))

        m = 1
        j = -1
        for i, x in enumerate(weights):
            if (weights[j+1][1] - weights[j][1]) < 0:
                weights_adj.append((x[0], m))
                m = m/float(2)
                j+=1
            else:
                weights_adj.append((x[0], m))
                j+=1

        # picking 10000 times
        #picked_list = weighted_pick(zip(*weights_adj)[1],1000000)

        sumOfWeights = sum(zip(*weights_adj)[1])
        probabilities = [(i/float(sumOfWeights)) for i in zip(*weights_adj)[1]]
        user_fractions = zip(zip(*weights_adj)[0], probabilities)
        d = dict(user_fractions)

        # plotting the histogram
        #hist(picked_list,bins=len(zip(*weights_adj)[1]),normed=1,alpha=.8,color='red')
        #show()

        assert len(d) == len(weights_adj) == len(weights) == len(sort_pos)

        for keys, values in d.items():
            gs_user_dist.setdefault(keys,[]).append(values)

        #-----------

        #temp = []
        #for keys,values in leaves.items():
        #    temp.append((keys, values[0]))
        #b = sorted(temp, lambda x,y: 1 if len(x[1])>len(y[1]) else -1 if len(x[1])<len(y[1]) else 0)
        #print "------------------"
        #for x in b:
        #    print "Guard set: %s\tPosition: %s" % (x[0], x[1])

        for keys, values in leaves.items():
            gs_dict_verb.setdefault(keys,[]).append(values[0])

        for x in guard_sets:
            gs_bw_dict.setdefault(x.__dict__["name"],[]).append(guard_set_bw(x))

        for x in guard_sets:
            date_gs_map.setdefault(x.__dict__["name"],[]).append(name)

        for x in guard_sets:
            gs_guards.setdefault(x.__dict__["name"],[]).append(x)

    #print gs_bw_pos

    gs_bw_dict_verb = {}
    for keys, values in gs_bw_dict.items():
        gs_bw_dict_verb[keys] = {
        'Bandwidth' : values,
        }

    gs_user_dist_verb = {}
    for keys, values in gs_user_dist.items():
        gs_user_dist_verb[keys] = {
        'Fraction of users' : values,
        }


    gs_dates = {}
    for keys, values in date_gs_map.items():
        gs_dates[keys] = {
        'Dates' : values,
        }

    gs_guards1 = {}
    for keys, values in gs_guards.items():
        gs_guards1[keys] = {
        'guards' : values,
        }

    assert len(gs_bw_dict_verb)== len(gs_user_dist_verb) == len(gs_dates)
    master = [gs_bw_dict_verb, gs_user_dist_verb, gs_dates, gs_guards1]
    d = {}
    for k in gs_bw_dict_verb.iterkeys():
        d[k] = tuple(d[k] for d in master)

    return d


#function to check if a list is in another list
def contains(small, big):
    new_big = big[:len(small)]
    if new_big == small:
        return True

def test_contains():
    print contains([1,2,3], [1,2,1,2,3])

def uniquify(L):
    found = []
    for item in L:
        if item not in found:
            found.append(item)
    return found




def test_uniquify():

    print uniquify([([1],2),([1],2)])

def merge_two_dicts( x, y):
    '''Given two dicts, merge them into a new dict as a shallow copy.'''
    z = x.copy()
    z.update(y)
    return z


def exploit_repair_phase(c, guard_sets, fix_Threshold=20 * 1000, MAxThreshold = 40*1000,  target_set = None):

    quanta = list_all_guard_quanta(c, Threshold=MAxThreshold)
    gs_bw = get_all_gs_bandwidth(c, guard_sets, Threshold=MAxThreshold)
    #rest_of_quanta = filter_used_quanta(quanta, guard_sets)

    gs2bw = [bw for (g,bw) in gs_bw if g.name == target_set]
    logging.debug("HD: the target bandwidth: %s",gs2bw  )



    broken_guard_sets = sorted([(bw, g, i) for i, (g, bw) in enumerate(gs_bw) if bw <= fix_Threshold])
    broken_names = [n2.name for (n1,n2,n3) in broken_guard_sets]
    if target_set in broken_names:
        return True
    else:
        return False

def find_best_candidadte(network, guard_sets, fix_Threshold=20 * 1000, MAxThreshold = 40*1000, targets = None):
    c = copy(network)
    quanta = list_all_guard_quanta(c.values(), Threshold=MAxThreshold)
    gs_bw = get_all_gs_bandwidth(c.values(), guard_sets, Threshold=MAxThreshold)
    rest_of_quanta = filter_used_quanta(quanta, guard_sets)
    gs2bw = dict((g.name, bw) for (g, bw) in gs_bw)


    broken_guard_sets = sorted([(bw, g, i) for i, (g, bw) in enumerate(gs_bw) if bw <= fix_Threshold])
    logging.debug("HD: the broken sets: %d", len(broken_guard_sets))
    rest_of_quanta = sorted(rest_of_quanta, key=lambda x: x.bw, reverse=True)
    fixed_guard_sets = copy(guard_sets)
    logging.debug("HD: the rest of quanta: %d", len(rest_of_quanta))
    ##################################################################
    to_me = []# list of broken sets till we reach the target
    for bw, gs, i in broken_guard_sets:
        logging.debug("HD: The broken set: %s\t\t\t bw:%f\t\t\t[%f,%f]", gs.name, bw, float(gs.BW_bounds[1]/float(2)),float(gs.BW_bounds[1]))
        if gs.name == targets:
            to_me.append(gs)
            logging.debug("HD: Stopped")
            break
        to_me.append(gs)
    ##################################################################
    target_gs = copy(to_me[-1])
    #del to_me[-1]
    [gmin, gmax] = target_gs.BW_bounds
    lower, upper = (gmax/float(2)), gmax
    logging.debug("HD: the broken sets before target set: %d, the target is %s with lower %f and upper %f", len(to_me), target_gs.name, float(lower), float(upper))
    ##################################################################
    cnt = 0
    adversary = []
    while cnt < len(to_me):
        s = to_me[cnt]
        added_guard = 0
        if cnt == 0:
            quanta = list_all_guard_quanta(c.values(), Threshold=MAxThreshold)
            gs_bw = get_all_gs_bandwidth(c.values(), guard_sets, Threshold=MAxThreshold)
            rest_of_quanta = filter_used_quanta(quanta, guard_sets)
            rest_of_quanta = sorted(rest_of_quanta, key=lambda x: x.bw, reverse=True)



        [gmin, gmax] = s.BW_bounds
        candidates = [q for q in rest_of_quanta if (gmax/float(2))<= q.bw<= gmax]
        logging.debug("HD: Candidate lists for: %s\tare:%s",s.name, [(j.bw,j.bw_fraction) for j in candidates])

        bw = gs2bw[s.name]
        guards = []
        while bw < MAxThreshold and len(candidates) > 0:
             bw += candidates[0].bw_fraction
             guards.append(float(candidates[0].bw))
             logging.debug("HD: Set %s \t\t Guard %f added", s.name, float(candidates[0].bw_fraction))
             rest_of_quanta.remove(candidates[0])
             del candidates[0]

        if bw >= MAxThreshold:
            logging.debug("HD: Set: %s\tBW: %f\tGood, no need to add bw ", s.name,float(bw))
            if cnt == (len(to_me) - 1):
                guards.sort()
                up = guards[-1]
                adversary.append(up - 1.0)
                added_guard = 1
                break
        else:
            logging.debug("HD: Set: %s needs more bandwidth\t\tBW: %f", s.name, float(bw))
            gmin = gmax/float(2)
            n =int(math.ceil((MAxThreshold - bw) /float(gmin)))
            adversary += [gmin]*n
            added_guard = 1
        cnt += 1
        if added_guard == 1: cnt = 0


        logging.debug("HD: adding adversary to the network for test")
        asn = '31549'
        if added_guard == 1:
            for mybw in adversary:
                name = hexlify(urandom(16))
                ip = None
                while (ip == None):
                    ip = classes.gimme_asn_database(asn)
                rly = {
                    "nickname":ip,
                    "ID": name,
                    "bandwidth": float(mybw),
                    "coord":None,
                    "geo": None,
                    "asn": asn,
                    "valid": None,
                    "isExit": True,
                    "isGuard": False,
                    "ip": ip,
                    "adversary": 1
                }

                c[ip] = rly
                logging.debug("HD: adv relay: %s with bw is added: %f", ip,mybw)







    if exploit_repair_phase(c.values(), guard_sets, target_set = targets):
        return adversary
    else:
        return []






'''
##################################################################
overlapped = []
for s in to_me:
    [gmin, gmax] = s.BW_bounds
    if gmax > lower and (gmax/float(2) < upper):
        logging.debug("HD: Set: %s: has overlap", s.name)
        overlapped.append(s)
logging.debug("HD: the broken sets have overlapped candidates with target set: %d", len(overlapped))

##################################################################
overlapped.append(target_gs)
assert(len(overlapped) >= 1)
need_fix = []
for s in overlapped:
    [gmin, gmax] = s.BW_bounds
    candidates = [q for q in rest_of_quanta if (gmax/float(2))<= q.bw<= gmax]
    logging.debug("HD: Candidate lists for: %s\tare:%s",s.name, [(j.bw,j.bw_fraction) for j in candidates])
    need_fix.append(candidates)
##################################################################
gs2bw = dict((g.name, bw) for (g, bw) in gs_bw)
bw_list = []
last = 999999999999999
used = Set([])


# 1- added guards should  be in [gmin,gmax]
# 2- added guards should be higher that previous guard set

adversary = []
for i in range(len(overlapped)):
    candidates = Set(need_fix[i]) - used
    candidates = list(candidates)
    if len(candidates) != 0: candidates = sorted(candidates, key= lambda x:x.bw, reverse=True)
    slower = overlapped[i].BW_bounds[1]/float(2)
    supper = overlapped[i].BW_bounds[1]
    logging.debug("HD: the broken set %s has %d candidate with upper %f and lower %f", overlapped[i].name, len(candidates),  float(supper), float(slower))
    logging.debug("HD: Now candidate lists for: %s\tare:%s",overlapped[i].name, [(j.bw,j.bw_fraction) for j in candidates])
    bw = gs2bw[overlapped[i].name]
    added_guards = []
    while bw < MAxThreshold and len(candidates) != 0:
        q = candidates[0]
        bw += q.bw_fraction
        added_guards.append(q.bw_fraction)
        used |= Set([q])
        logging.debug("HD: Candidate guard %f is added to the broken set %s with upper %f and lower %f",float(q.bw_fraction), overlapped[i].name,  float(supper), float(slower))
        del candidates[0]

    #1 we still need more bandwidth
    if (len(added_guards) != 0):
        l,u = added_guards[-1], added_guards[0]
        logging.debug("HD: in the broken set %s, %d candidates used",overlapped[i].name, len(added_guards))
        if (i == len(overlapped) - 1) and bw > MAxThreshold:
            tmp = l + 0.5
            if tmp > supper: tmp = float(slower)
            bw -= l
            bw += tmp
            adversary.append(tmp)
            del added_guards[-1]
            added_guards.append(tmp)
            for q in used:
                if q.bw_fraction == l:
                    dt = q
            logging.debug("HD: Quanta %s removed", dt.name)
            used.remove(dt)
            logging.debug("HD: Adv guard %f is added to the broken set %s with upper %f and lower %f",float(tmp), overlapped[i].name, float(supper), float(slower))

        while bw < MAxThreshold:
            tmp = float(l + 1)
            if tmp > supper: tmp = float(slower)
            bw += tmp
            adversary.append(tmp)
            added_guards.append(tmp)
            logging.debug("HD: Adv guard %f is added to the broken set %s with upper %f and lower %f",float(tmp), overlapped[i].name, float(supper), float(slower))
    else:
        st = slower + 1.0
        if i != 0:
            if (last - 1) > slower and (last - 1) < supper: st = float(last -1)
        logging.debug("HD: in the broken set %s did not used candidates, adv guards are added with bw %f ",overlapped[i].name, float(st))
        while bw < MAxThreshold:
            tmp = st
            if tmp > supper: tmp = float(slower)
            bw += tmp
            adversary.append(tmp)
            added_guards.append(tmp)
            logging.debug("HD: Adv guard %f is added to the broken set %s with upper %f and lower %f",float(tmp), overlapped[i].name,  float(supper), float(slower))


    added_guards.sort()
    last = float(added_guards[-1])
    logging.debug("HD: In the broken set %s  var last is set to %f ", overlapped[i].name, last)

return adversary
'''



def test_comm_adv_merge(gsTree,c,corrupted_gs,all_users,day_counter,file_name,anon_loging, NU = 500000, KTR = 20000,CTR = 40000, advs = None, relays_adv = {}, IamCompromised = 0,waiting_days=0,IamBroken= None):

    # For targeted attack I have to infect this guard set
    # We have to check whether this set is in the brocken ones
    logging.debug("HD: We are in BW design code: relays: %d, adv relays: %d adv type: %d", len(c), len(relays_adv), advs)
    c.update(relays_adv)
    logging.debug("HD: Relays are updated %d ", len(c))
    #c = c.values()
    quanta = list_all_guard_quanta( c.values(),Threshold=CTR) # done
    guard_sets = gsTree.get_GSs()

    if advs == 12:
        # first find whether the target is compromised or N0T?

        target_user  = [all_users[0]]
        target_set_names = []
        myleaves = gsTree.get_Leafs()
        logging.debug("HD: target  users: %s", target_user)
        #find the corrupted sets:
        badguards = dict((g, []) for g in relays_adv)
        badsets = {}
        for k, v in badguards.items():# k is ip
            #a = [x.__dict__["name"] for x in guard_sets if k in x.__dict__["guards"]]
            for x in guard_sets:
                for g in x.__dict__["guards"]:
                    if k == g.name:
                        if (x.__dict__["name"]) not in badsets: badsets[x.__dict__["name"]] = []
                        badsets[x.__dict__["name"]].append(g.name)

        logging.debug("HD: compromised sets: %s", badsets)


        #find the target set
        for b in myleaves:
            values = myleaves[b][0]
            i = bisect.bisect_left(target_user, tuple(values))
            j = bisect.bisect_right(target_user, tuple(values+[1]*23))
            if i != j:
                target_set_names.append((b,tuple(values)))
                #print target_user, values

        logging.debug("HD: target set: %s", target_set_names)
        # target is compromised or not?
        if len(target_set_names) != 0:
            if target_set_names[0][0] in badsets:
                #user is compromised, now update the relay bandwidth
                print "Target Compromised"
                logging.debug("HD: target is compromised, update the adv's bandwidth ")
                for bad in badsets:
                    for g in badsets[bad]:
                        if bad == target_set_names[0][0]:
                            relays_adv[g]["bandwidth"] = KTR + 10.0
                            c[g]["bandwidth"]  = KTR + 10.0
                            logging.debug("HD: adv relay in the target set: %s \t update bw to : %f",g, KTR + 10.0)
                        else:
                            relays_adv[g]["bandwidth"]  = 20.0
                            c[g]["bandwidth"] = 20.0
                            logging.debug("HD: adv relay NOT in the target set: %s \t update bw to : %f",g, 20.0)


            else:
                # wait to the set is about to break
                logging.debug("HD: the set is not compromised, get adv relays out of the network then add new one")
                # delete adv relays because they are useless we should add new ones
                for g in relays_adv:
                    if g in c:
                        del c[g]
                relays_adv = {}

                target_broken_flag = exploit_repair_phase( c.values(), guard_sets, MAxThreshold= CTR,target_set= target_set_names[0][0])#
                logging.debug("HD: the set is broken? %s",target_broken_flag )
                if target_broken_flag:
                    if IamBroken == None: IamBroken = 1
                    print "Target Broken"
                    logging.debug("HD: the traget set is about to break")
                    # our target set is about to break it's time to get in that set
                    # first analyze all the candidates
                    advbw = find_best_candidadte(c, guard_sets, MAxThreshold= CTR, targets=target_set_names[0][0])
                    logging.debug("HD: the best candidate has bandwidth %s", advbw)
                    asn = '31549'
                    for mybw in advbw:
                        name = hexlify(urandom(16))
                        ip = None
                        while (ip == None):
                            ip = classes.gimme_asn_database(asn)
                        rly = {
                            "nickname":ip,
                            "ID": name,
                            "bandwidth": float(mybw),
                            "coord":None,
                            "geo": None,
                            "asn": asn,
                            "valid": None,
                            "isExit": True,
                            "isGuard": False,
                            "ip": ip,
                            "adversary": 1
                        }

                        relays_adv[ip] = rly
                        logging.debug("HD: adv relay: %s with bw is added: %f", ip,mybw)
                    c.update(relays_adv)



    c = c.values()
    logging.debug("HD: Relays now are updated %d ", len(c))
    quanta = list_all_guard_quanta( c,Threshold=CTR) # done


    ## Fix them, if possible!
    fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets, fix_Threshold=KTR,MAxThreshold= CTR)#Done
    assert len(fixed_guard_sets) == len(guard_sets)
    for gs in fixed_guard_sets:
        assert isinstance(gs, GuardSet)

    guard_sets = fixed_guard_sets

    gsTree.update_GSs(guard_sets)

    # # Detect the weak ones, kill them off
    gs_bw = get_all_gs_bandwidth(c, guard_sets,Threshold = CTR)
    Kill_threshold = KTR

    killed_guard_sets = [g for g, bw in gs_bw if bw < Kill_threshold]
    num_killed = len(killed_guard_sets)

    gsTree.delete_GSs(killed_guard_sets)


    ## Make new GSs
    guard_sets = gsTree.get_GSs()

    rest_of_quanta = filter_used_quanta(quanta, guard_sets)

    min_f = 0.0
    randomized=False
    new_sets, spare_quanta = new_guard_sets(rest_of_quanta, Threshold=CTR,min_f=min_f, randomized=randomized)
    logging.debug("BWdsign:CREATED:%d:DAY:%d", len(new_sets), day_counter)
    gsTree.add_GSs(new_sets)

    guard_sets = gsTree.get_GSs()
    leaves = gsTree.get_Leafs()
    median_bw = median_guard_set_bw(guard_sets) #mohsen

    #logging some guard sets' information
    temp = []
    cnt_gs = 0
    logging.info("BWDESIGN:Number of guardsets:%d",len(guard_sets))
    for x in guard_sets:
        sum_bw = 0
        cnt_g = 0
        txt = "BWDAY:STABE:{0}:GS:{1}:".format(day_counter,x.name)
        logging.info("%s",txt)
        for i in x.__dict__["guards"]:
            sum_bw = sum_bw + i.bw_fraction
            cnt_g += 1
            txt = "BWDAY:{0}:GS:{1}:G:{2}:BW:{3}".format(day_counter,cnt_gs,cnt_g,i.bw_fraction)
            logging.info("%s",txt)
        cnt_gs += 1





    mybandwidth = my_guard_set_bw(guard_sets)
    #--------------
    if advs == 12:
        corrupted_gs = dict((k,[]) for k in relays_adv)
        for k, v in corrupted_gs.items():# k is ip
            #a = [x.__dict__["name"] for x in guard_sets if k in x.__dict__["guards"]]
            a = []
            for x in guard_sets:
                for g in x.__dict__["guards"]:
                    if k == g.name: a.append(x.__dict__["name"] )
            corrupted_gs[k].extend(a)
    else:
        #--------------
        for k, v in corrupted_gs.items():
            a = []
            for x in guard_sets:
                for g in x.__dict__["guards"]:
                    if k == g.name: a.append(x.__dict__["name"] )
            corrupted_gs[k].extend(a)
        #---------------


    #creat new date key
    timeline = []


    #loops over guard set positions checking comrpomised guard sets against user id's created
    bs = set()
    for _, b in corrupted_gs.items():
        bs |= set(b)

    bs &= set([keys for keys in leaves])
    # print len(bs)

    #for keys, values in leaves.items():
    #    for _, b in corrupted_gs.items():
    #        if keys in b:
    # print "users:", users.keys()
    #all_users = users['uncompromised']
    #if tt == 5: break
    #print 'length leaves',len(leaves)
    #print [leaves[keys][0] for keys in leaves]



    if day_counter % 29 == 1 and anon_loging == True:
        log_file = open(file_name,'a')
        for keys in leaves:
            tmp_str = ""
            content = leaves[keys][1].content
            for g in content.guards:
                tmp_str += " | name:{0}:id:{1}:bw:{2}:bw_fraction:{3}".format(g.name, g.id, g.bw, g.bw_fraction)
            myoutline = "{0}:{1}".format("JAMIE-SETS:DAY:{0}:SET:{1}:".format(day_counter, leaves[keys][0]), tmp_str)
            log_file.write("{0}\n".format(myoutline))

        for bandw in mybandwidth:
            log_file.write("BW-JAMIE-SETS-BW:DAY:{0}:BW:{1}:\n".format(day_counter,bandw))
        log_file.close()

    for b in bs:
                #print leaves[b]
                values = leaves[b][0]
                #print 'values: ', values
                i = bisect.bisect_left(all_users, tuple(values))
                # len_users = len(all_users)
                # affected = 0
                #
                # while i < len_users and all_users[i][:len(values)] == tuple(values):
                #     timeline[name].append(all_users[i])
                #     i += 1
                #     affected += 1

                j = bisect.bisect_right(all_users, tuple(values+[1]*23))
                timeline =  all_users[i:j] + timeline
                # print "compromized %s" % b

                # print i, j
                # print affected

                #for key, value in users.items():
                #    for x in value:
                #        # print x
                #        #if values == x[:len(values)]:
                #        if contains(small=values, big=x):
                #            timeline[name].append(x)


    target_user  = [all_users[0]]
    target_set_names = []
    myleaves = gsTree.get_Leafs()
    #find the corrupted sets:
    badguards = dict((g, []) for g in relays_adv)
    badsets = {}
    for k, v in badguards.items():# k is ip
        #a = [x.__dict__["name"] for x in guard_sets if k in x.__dict__["guards"]]
        for x in guard_sets:
            for g in x.__dict__["guards"]:
                if k == g.name:
                    if (x.__dict__["name"]) not in badsets: badsets[x.__dict__["name"]] = []
                    badsets[x.__dict__["name"]].append(g.name)


    #find the target set
    for b in myleaves:
        values = myleaves[b][0]
        i = bisect.bisect_left(target_user, tuple(values))
        j = bisect.bisect_right(target_user, tuple(values+[1]*23))
        if i != j:
            target_set_names.append((b,tuple(values)))
            #print target_user, values

    logging.debug("HD: target set at the end of the day: %s", target_set_names)
    # target is compromised or not?
    if IamBroken == 1: waiting_days += 1
    if len(target_set_names) != 0:
        if (target_set_names[0][0] in badsets) and (IamCompromised == 0) and advs == 12:

            bw = 0.0
            for ip in relays_adv:
                bw += relays_adv[ip]["bandwidth"]
            IamCompromised = 1
            log_file = open(file_name,'a')
            log_file.write("JAMIE-TARGETED-ATTACK:DAY:{0}:N-ADV:{1}:BW:{2}:DAYS:{3}:\n".format(day_counter,len(relays_adv),bw,waiting_days))
            log_file.close()
    if advs != 12: assert (len(relays_adv) == 0)
    return gsTree,timeline, median_bw,len(guard_sets), relays_adv, IamCompromised,waiting_days,IamBroken

def test_comm_adv(adv_frac=0.01, NU = 500000):
    gsTree = GuardSetTree()

    #make this for every beginning of month of consensus not just 01/01/13
    c = parse_consensus1(file("../consensus/all/2015-01-01-00-00-00-consensus").read())["relays"]

    total_guard_bw = sum(entry['bandwidth'] for entry in c.values())

    #adversary guards
    adv_guards = sample_Adv(c, adv_frac*total_guard_bw, include_guards=[])

    corrupted_gs = dict((g,[]) for g in adv_guards)

    users = {"uncompromised": []}
    N = NU#1000000
    for i in range(N):
        idx = np.random.randint(0,2,23)
        users["uncompromised"].append(tuple(idx))

    users["uncompromised"] = sorted(users["uncompromised"])

    # dictionary of compromised users at every date
    timeline = collections.OrderedDict()

    #print
    tt = 0
    for name, c in all_consensuses():
        # add adversary to the network here

        #print name
        c = merge_two_dicts(c, adv_guards)
        c = c.values()
        quanta = list_all_guard_quanta(c)
        guard_sets = gsTree.get_GSs()

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        gsTree.update_GSs(guard_sets)

        # # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        killed_guard_sets = [g for g, bw in gs_bw if bw < Kill_threshold]
        num_killed = len(killed_guard_sets)

        gsTree.delete_GSs(killed_guard_sets)


        ## Make new GSs
        guard_sets = gsTree.get_GSs()

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)
        gsTree.add_GSs(new_sets)

        guard_sets = gsTree.get_GSs()
        leaves = gsTree.get_Leafs()

        #--------------

        for k, v in corrupted_gs.items():# k is ip
            #a = [x.__dict__["name"] for x in guard_sets if k in x.__dict__["guards"]]
            a = []
            for x in guard_sets:
                for g in x.__dict__["guards"]:
                    if k == g.name: a.append(x.__dict__["name"] )
            corrupted_gs[k].extend(a)


        #creat new date key
        timeline.setdefault(name,[])


        #loops over guard set positions checking comrpomised guard sets against user id's created
        bs = set()
        for _, b in corrupted_gs.items():
            bs |= set(b)

        bs &= set([keys for keys in leaves])
        # print len(bs)

        #for keys, values in leaves.items():
        #    for _, b in corrupted_gs.items():
        #        if keys in b:
        # print "users:", users.keys()
        all_users = users['uncompromised']
        tt += 1
        #if tt == 5: break
        for b in bs:
                    #print leaves[b]
                    values = leaves[b][0]

                    i = bisect.bisect_left(all_users, tuple(values))
                    # len_users = len(all_users)
                    # affected = 0
                    #
                    # while i < len_users and all_users[i][:len(values)] == tuple(values):
                    #     timeline[name].append(all_users[i])
                    #     i += 1
                    #     affected += 1

                    j = bisect.bisect_right(all_users, tuple(values+[1]*23))
                    timeline[name] =  all_users[i:j] + timeline[name]
                    # print "compromized %s" % b

                    # print i, j
                    # print affected

                    #for key, value in users.items():
                    #    for x in value:
                    #        # print x
                    #        #if values == x[:len(values)]:
                    #        if contains(small=values, big=x):
                    #            timeline[name].append(x)


    #uniquify lists in key values of timeline and turn in to a nested list ---- note the uniquify list should do nothing since these lists should be unique already

    year_comp = {}
    temp_big_list = set()
    for i, (k, v) in enumerate(timeline.items()):
        temp_big_list |= set(v)
        year_comp[k]=  float(len(temp_big_list)) / float(N)

    # forward append compromised users to all future dates

    # prev = []
    # for i,el in enumerate(temp_big_list):
    #     el_new = (el[0], prev + el[1])
    #     prev += el[1]
    #     temp_big_list[i] = el_new



    # uniquify lists after forward appending and get fractions

    # year_comp = []
    # for i, x in enumerate(temp_big_list):
    #     #year_comp.append((x[0], len(uniquify(x[1]))/float(500)))
    #     unique = [list(j) for j in set(tuple(j) for j in x[1])]
    #     year_comp.append((x[0], len(unique)/float(10000)))

    return year_comp


def test_consensus_minmaxpos():
    prev_quanta = []
    gsTree = GuardSetTree()
    date_gs_map = {}
    minpos = []
    maxpos = []
    print
    for name, c in all_consensuses():
        quanta = list_all_guard_quanta(c)

        guard_sets = gsTree.get_GSs()

        ## Fix them, if possible!
        fixed_guard_sets, (broken_id, fixed_id) = fix_guard_sets(c, guard_sets)
        assert len(fixed_guard_sets) == len(guard_sets)
        for gs in fixed_guard_sets:
            assert isinstance(gs, GuardSet)

        guard_sets = fixed_guard_sets

        gsTree.update_GSs(guard_sets)

        # # Detect the weak ones, kill them off
        gs_bw = get_all_gs_bandwidth(c, guard_sets)
        Kill_threshold = 20000

        killed_guard_sets = [g for g, bw in gs_bw if bw < Kill_threshold]
        num_killed = len(killed_guard_sets)

        gsTree.delete_GSs(killed_guard_sets)

        ## Make new GSs
        guard_sets = gsTree.get_GSs()

        for x in guard_sets:
            date_gs_map.setdefault(x.__dict__["name"],[]).append(name)

        rest_of_quanta = filter_used_quanta(quanta, guard_sets)

        min_f = 0.0
        randomized=False
        new_sets, spare_quanta = new_guard_sets(rest_of_quanta, min_f=min_f, randomized=randomized)
        gsTree.add_GSs(new_sets)

        guard_sets = gsTree.get_GSs()
        leaves = gsTree.get_Leafs()

        position = []
        for keys, values in leaves.items():
            position.append(len(values[0]))
        maxpos.append(max(position))
        minpos.append(min(position))

    print maxpos
    print minpos

    diff = [x - y for x, y in zip(maxpos, minpos)]
    print max(diff), min(diff)
    print diff

def evaluate(frac = 0.0, NU = 500000):
    N = 100
    if True:
        tmpdic = {}
        for i in range(N):
            print " adversary with fraction {0}, {1}".format(frac,i)
            tmpdic[i] = test_comm_adv(frac, NU)
        dates = tmpdic[0].keys()
        dates.sort()
        file_ = open("output-{0}".format(frac),'w')
        for d in dates:
            l = []
            for i in range(N):
                l.append(tmpdic[i][d])
            file_.write("{0},{1},{2},{3},{4},{5},{6},{7},{8},\n".format(d,min(l),max(l),np.mean(l),np.median(l),np.percentile(l,10),np.percentile(l,25),np.percentile(l,75),np.percentile(l,90)))
            print "{0},{1},{2},{3},{4},{5},{6},{7},{8}".format(d,min(l),max(l),np.mean(l),np.median(l),np.percentile(l,10),np.percentile(l,25),np.percentile(l,75),np.percentile(l,90))
        file_.close()




# timing tests ------ #

if __name__ == "__main__":
    '''
    import line_profiler
    profiler = line_profiler.LineProfiler()
    profiler.add_function(test_comm_adv)
    profiler.run('test_comm_adv()')
    profiler.print_stats()
    '''
    #test_comm_adv(adv_frac=0.5)
    #test_single_adv()
    for i in [0.0]:#,0.01,0.05,0.1]:
        evaluate(frac=i)
#cProfile.run('test_algo3()')
