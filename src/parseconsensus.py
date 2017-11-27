#!/usr/bin/env python

import requests
import re
import json
import sys
from  itertools import izip
import random
from copy import copy
from random import randint, seed, shuffle
from itertools import cycle,chain
from operator import add, neg
import numpy as np
import numpy

# parse consensus for nicknames, guard flag (and others) and bandwidth
def parse_consensus1(consensus):
    relays1 = {'relays' : []}
    tmp_relays = {}
    # parse out the nickname, guard flag and bandwidth
    #regex1 = re.compile(ur'r\s(?P<nickname>\w+\s[^\s]+)\b.*\n(?:^a.*\n)?^s\s(?P<type>.*\bGuard\b.*)\n^v\s.*\n^w\sBandwidth=(?P<bandwidth>[0-9]+)', re.MULTILINE | re.VERBOSE)
    regex1 = re.compile(r'^r\s(?P<nickname>\w+\s[^\s]+).*\s(?P<ip>\d*[.]\d*[.]\d*[.]\d*)\s.*\ns\s(?P<type>.*\bGuard\b.*).*\nv\s.*\nw\sBandwidth=(?P<bandwidth>[0-9]+)', re.MULTILINE)
    # Find all the matches in the consenses
    # matches = regex.finditer(consensus)
    for record in regex1.finditer(consensus):
        if 'Exit' in record.group('type'): continue
        # For each record, create a dictionary object for the relay
        relay1 = {
            'nickname' : record.group('nickname'),
            'type' : record.group('type').split(),
            'bandwidth' : int(record.group('bandwidth')),
            'ip' : record.group('ip')

        }
        if relay1['ip'] in tmp_relays:
            tmp_relays[relay1['ip']]['bandwidth'] += relay1['bandwidth']
        else:
            tmp_relays[relay1['ip']] = relay1
        # And append it to the master list
    relays1['relays'] = tmp_relays
    return relays1

# parse cosensus without nickname to allow us to find the total bw with no false positives (arising from numbers in nicknames)
def parse_consensus2(consensus):
    relays2 = {'relays' : []}

    # parse out the nickname, guard flag and bandwidth
    regex2 = re.compile(ur'r\s(?P<nickname>\w+)\b.*\n(?:^a.*\n)?^s\s(?P<type>.*\bGuard\b.*)\n^v\s.*\n^w\sBandwidth=(?P<bandwidth>[0-9]+)', re.MULTILINE | re.VERBOSE)

    # Find all the matches in the consenses
    # matches = regex.finditer(consensus)
    for record in regex2.finditer(consensus):
      # For each record, create a dictionary object for the relay
      relay2 = {
      'type' : record.group(2).split(),
      'bandwidth' : int(record.group(3)),
      }
      # And append it to the master list
      relays2['relays'].append(relay2)
    return relays2

# this gives the total bandwidth of guards in the consensus
def total_bw(guards):
    total_guard_bw = sum(entry['bandwidth'] for entry in guards["relays"])
    return total_guard_bw

def adversary_bw(amount):
    amount = 0.05 * total_guard_bw # change to any % we want

## --------- George's experiments ------------

def sample_Adv(guards, Adv_bw, include_guards=[]):
    relays = copy(guards["relays"])
    random.shuffle(relays) # Pick a random new order
    Adv_relays = []
    Current_bw = 0

    existing = set([e["nickname"] for e in include_guards])
    Current_bw = sum([e["bandwidth"] for e in include_guards], 0)

    for r in relays:
      if r["bandwidth"] + Current_bw <= Adv_bw and r["nickname"] not in existing:
        Adv_relays += [r]
        Current_bw += r["bandwidth"]
        existing.add(r["nickname"])

    return Adv_relays

def sample_User(guards, exclude_guards=[]):
    excluded = set(e["nickname"] for e in exclude_guards)

    relays = copy(guards["relays"])
    #random.shuffle(relays) # Pick a random new order
    #for r in relays:
    while True:
        r = random.choice(relays)
        if r["nickname"] not in excluded:
            return r
    raise Exception("A guard should have been found!")

def get_strategic_moves(guards, Adv_bw, samples, player=0, steps=100):
    assert player == 0 or player == 1
    User_move = sample_User(guards)
    moves = []
    counter = 0
    while len(moves) < samples:
      counter += 1
      Adv_move = sample_Adv(guards, Adv_bw, [User_move])
      User_move = sample_User(guards, Adv_move)
      if counter % steps == 0:
        which_move = [User_move, Adv_move][player]
        moves += [which_move]

    return moves


## --------- Jamie's experiments ------------

# this lists guard bw's in descending order
def sort_guards(guards):
    sorted_guards = sorted((entry['bandwidth'] for entry in guards["relays"]), reverse=True) #sort guards in descending list of bandwidths
    return sorted_guards

## -----------

## this lists guard bw's in descending order with associated nickname and JSON left untouched - easier to read
def sort_guards_with_input(guards):
    json_source = json.dumps(guards)
    data = json.loads(str(json_source))
    data['relays'].sort(key=lambda item: item['bandwidth'], reverse=True)
    return data

# this creates a list with elements nicknames and associated bw (in descending order) where input is given by sorted json from the above function
def get_sorted_names_bw(guards):
  #sorted_guards_bw = list(entry['bandwidth'] for entry in guards["relays"])
  #sorted_guards_names = list(d['nickname'] for d in guards["relays"])
  #temps = [None]*(len(sorted_guards_bw)+len(sorted_guards_names))
  #temps[::2] = sorted_guards_bw
  #temps[1::2] = sorted_guards_names
  #print temps
  #sorted_grds_w_names = [temps[i:i+2] for i in range(0, len(temps), 2)]
  # print sorted_grds_w_names

  # Version 2
  sorted_grds_w_names = [[entry['bandwidth'], entry['nickname']] for entry in guards["relays"]]
  # sorted_grds_w_names = sorted(sorted_grds_w_names, reverse=True)
  #assert sorted_grds_w_names == sorted_grds_w_names2

  return sorted_grds_w_names

## -----------

# option 1: simple function to group guards in to guard sets based on thresholds
# gets guardsets w associated nicknames, and guarantees the last set is above the threshold., guarantess each guard bgger than bandwidth has more than one user group by creating duplicate guardsets
def guardset_w_names(sorted_guards, lim):
    guardsets = []
    temp_size = 0
    temp_set = []
    for i in sorted_guards:
        if i[0] > lim:
            num = int(i[0] / lim)
            for _ in range(num):
              guardsets.append([i])
        else:
            temp_size += i[0]
            temp_set.append(i)
            if temp_size > lim:
                guardsets.append(temp_set)
                temp_size = 0
                temp_set = []
    if temp_set != []:
        guardsets[-1].extend(temp_set)

    return guardsets

## -----------

#option 2: groups guards together with similar means, and caps the number of guards in a guard set

#the setup
def chunks(q, n):
    q = list(q)
    for i in range(0, len(q), n):
       yield q[i:i+n]

def shuffle(q, n):
    q = list(q)
    m = len(q)//2
    left =  list(chunks(q[:m],n))
    right = list(chunks(reversed(q[m:]),n)) + [[]]
    return chain(*(a+b for a,b in zip(left, right)))

def listarray(n):
    return [list() for _ in range(n)]

def mean(q):
    return sum(q)/len(q)

def report(q):
    for x in q:
        print [mean(x), len(x), x]

#the meat
def get_guardset2(guards):
    sorted_guards = sorted((entry['bandwidth'] for entry in guards["relays"]), reverse=True)
    data = sorted_guards
    SIZE = 30 #change to whatever we want. Do we want a limit on the number guards in a guard set?
    COUNT = len(data)
    NBUCKETS = (COUNT+SIZE-1) // SIZE

    order = shuffle(range(COUNT), NBUCKETS)
    posts = cycle(range(NBUCKETS))
    buckets = listarray(NBUCKETS)
    for o in order:
        i = posts.next()
        buckets[i].append(data[o])
    return report(buckets)
    listofgs = mean(data)
    return listofgs

## -----------

#defining relationship between guard sets and user groups.

## -----------

#this splits users randomly in to similar sized user groups, with the number of user groups == number of guard sets (sensible for static case??)
def get_user_groups(users, num_guard_sets):
    #lstusers = list(range(users))
    #random.shuffle(lstusers)
    #userlen = len(lstusers)
    #size = int(userlen / num_guard_sets)
    #user_groups = [lstusers[0+size*i : size*(i+1)] for i in xrange(num_guard_sets)]
    #leftover = userlen - size*num_guard_sets
    #edge = size*num_guard_sets
    #for i in xrange(leftover):
      #user_groups[i%num_guard_sets].append(lstusers[edge+i])
    #return user_groups
    # Version 2
    lstusers = list(range(users))
    random.shuffle(lstusers)
    user_groups = [[] for _ in range(num_guard_sets)]
    for i in range(0, users):
        d1 = random.randint(0,num_guard_sets-1)
        user_groups[d1].extend([i])
    return user_groups

#this randomly picks a guard set and randomly picks a user group and creates an assignment between them.
def user_groups_to_guard_sets(user_groups, guard_sets):
    #rand_user_groups = []
    #rand_gs = []
    #index_shuf1 = range(len(user_groups))
    #random.shuffle(index_shuf1)
    #index_shuf2 = range(len(guard_sets))
    #random.shuffle(index_shuf2)
    #for i in index_shuf1:
    #  rand_user_groups.append(user_groups[i])
    #for j in index_shuf2:
    #  rand_gs.append(guard_sets[j])
    #temp = [None]*(len(rand_user_groups)+len(rand_gs))
    #temp[::2] = rand_user_groups
    #temp[1::2] = rand_gs
    #ug_to_gs = [temp[i:i+2] for i in range(0, len(temp), 2)]

    # Version 2
    assert len(guard_sets) == len(user_groups)
    user_groups_new = user_groups + []
    random.shuffle(user_groups_new)
    pairs = zip(user_groups_new, guard_sets)
    # print "Called!"

    return pairs

## -----------

#find mixed strategy

#pay off matrix finder - zero sum - 0 if guard in guardset, 1 otherwise
def get_payoff_matrix(sorted_guards, sorted_guardsets):
  c = 0
  l = []
  for c in range(len(sorted_guards)):
    for item in sorted_guardsets:
      if sorted_guards[c] in item:
          l.extend('0')
      elif sorted_guards[c] not in item:
          l.extend('1')
  chunks = [l[x:x+len(sorted_guardsets)] for x in xrange(0, len(l), len(sorted_guardsets))]
  payoff_matrix = numpy.matrix(chunks)
  intchunks = [map(int, x) for x in chunks]
  int_payoff_matrix = numpy.matrix(intchunks)
  return intchunks

## -----------

# sorts guards from a random sample of guardsets
def get_guards_from_rand_guardsets(guardsets):
    guardz =[]
    for i in guardsets:
        for j in i:
            guardz.append(j)
    return sorted(guardz)

## -----------

#this gives an example of approx mixed strategy solution

''' Approximate the strategy oddments for 2 person zero-sum games of perfect information.

Applies the iterative solution method described by J.D. Williams in his classic
book, The Compleat Strategyst, ISBN 0-486-25101-2.   See chapter 5, page 180 for details. '''

def solve(payoff_matrix, iterations=3):
    'Return the oddments (mixed strategy ratios) for a given payoff matrix'
    transpose = zip(*payoff_matrix)
    numrows = len(payoff_matrix)
    numcols = len(transpose)
    row_cum_payoff = [0] * numrows
    col_cum_payoff = [0] * numcols
    colpos = range(numcols)
    rowpos = map(neg, xrange(numrows))
    colcnt = [0] * numcols
    rowcnt = [0] * numrows
    active = 0
    for i in xrange(iterations):
        rowcnt[active] += 1
        col_cum_payoff = map(add, payoff_matrix[active], col_cum_payoff)
        active = min(zip(col_cum_payoff, colpos))[1]
        colcnt[active] += 1
        row_cum_payoff = map(add, transpose[active], row_cum_payoff)
        active = -max(zip(row_cum_payoff, rowpos))[1]
    value_of_game = (max(row_cum_payoff) + min(col_cum_payoff)) / 2.0 / iterations
    matrix = np.matrix(payoff_matrix)
    return rowcnt, colcnt, value_of_game


## -------------------------------------------

if __name__ == "__main__":
    consensus = file(sys.argv[1]).read()
    relays1 = parse_consensus1(consensus)
    relays2 = parse_consensus2(consensus)
    open(r'../scratch/tor_relays.txt','w').write(json.dumps(relays1, indent=4))
    open(r'../scratch/tor_relays_without_nickname.txt','w').write(json.dumps(relays2, indent=4))

    ## TODO step by step:
    ## - Given an adversary bandwidth limit,
    ##   generate random guard groups that may be compromised.
    ## - Given a user pick a random guard set.
    ## - Given a set of adv. strategies, and a user strategies
    ##   compute the equlibrium. (Use magic script).
    ##   How: Use above to sample Adv. and User strategies,
    ##   find eqiuilib. repeat many times.
