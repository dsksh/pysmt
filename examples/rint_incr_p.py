import os
import argparse
import re
import multiprocessing as mp

from time import sleep

from z3 import *

def assert_rint_constants(solver, decls, precs, ps_prev, eb, sb):
    is_improved = False
    is_mp = len(precs) >= 2

    for i in range(len(precs)):
        eb0, sb0 = precs[i]
        if eb < eb0 and sb < sb0:
            eb_ = eb
            sb_ = sb
        else:
            eb_ = eb0
            sb_ = sb0

        if eb_ != ps_prev[i][0] and sb_ != ps_prev[i][1]:
            ps_prev[i] = (eb_, sb_)
            is_improved = True

        emax = 2**(eb_-1)-1
    
        #max_value_v = (2**sb_-1) * 2**(emax-sb_+1)
        #if not is_mp:
        #    s = '(assert (= ri.max_value %d.))' % max_value_v
        #else:
        #    s = '(assert (= (ri.max_value %d) %d.))' % (i, max_value_v)
        #solver.add( parse_smt2_string(s, decls=decls) )
    
        normal_bound_d = 2**(emax-1)
        #if not is_mp:
        #    s = '(assert (= ri.normal_bound (/ 1.0 %d.)))' % normal_bound_d
        #else:
        #    s = '(assert (= (ri.normal_bound %d) (/ 1.0 %d.)))' % (i, normal_bound_d)
        #solver.add( parse_smt2_string(s, decls=decls) )
    
        err_denom_v = 2**(sb_-1)
        if not is_mp:
            s = '(assert (= ri.err_denom %d.))' % err_denom_v
        else:
            s = '(assert (= (ri.err_denom %d) %d.))' % (i, err_denom_v)
        solver.add( parse_smt2_string(s, decls=decls) )
    
        err_min_1 = 2**(sb_+emax-2)
        if not is_mp:
            #s = '(assert (= ri.err_min (/ %d. %d.)))' % (err_denom_v-1, normal_bound_d*err_denom_v)
            s = '(assert (= ri.err_min (/ 1 %d)))' % err_min_1
        else:
            #s = '(assert (= (ri.err_min %d) (/ %d. %d.)))' % (i, err_denom_v-1, normal_bound_d*err_denom_v)
            s = '(assert (= (ri.err_min %d) (/ 1 %d)))' % (i, err_min_1)
        solver.add( parse_smt2_string(s, decls=decls) )

    return is_improved

#

def solve(queue, args, precs, smt2_file, is_dplus):
    # Preparation.
    solver = SolverFor("QF_LIRA")

    # The SMT-LIB script should be loaded at once.

    if args.pset == 0:
        ast = parse_smt2_file(smt2_file)

    else:
        if len(precs) == 0:
            # TODO
            precs.append((11, 53))
        
        if len(precs) == 1:
            solver.add( parse_smt2_string('(declare-const ri.max_value Real)') )
            #solver.add( parse_smt2_string('(declare-const ri.normal_bound Real)') )
            solver.add( parse_smt2_string('(declare-const ri.err_denom Real)') )
            solver.add( parse_smt2_string('(declare-const ri.err_min Real)') )
            solver.add( parse_smt2_string('(declare-const ri.large_value Real)') )
        
            max_value = Real('ri.max_value')
            #normal_bound = Real('ri.normal_bound')
            err_denom = Real('ri.err_denom')
            err_min = Real('ri.err_min')
            large_value = Real('ri.large_value')
        elif len(precs) > 1:
            solver.add( parse_smt2_string('(declare-fun ri.max_value (Int) Real)') )
            #solver.add( parse_smt2_string('(declare-fun ri.normal_bound (Int) Real)') )
            solver.add( parse_smt2_string('(declare-fun ri.err_denom (Int) Real)') )
            solver.add( parse_smt2_string('(declare-fun ri.err_min (Int) Real)') )
            #solver.add( parse_smt2_string('(declare-fun ri.large_value (Int) Real)') )
            solver.add( parse_smt2_string('(declare-const ri.large_value Real)') )
        
            max_value = Function('ri.max_value', IntSort(), RealSort())
            #normal_bound = Function('ri.normal_bound', IntSort(), RealSort())
            err_denom = Function('ri.err_denom', IntSort(), RealSort())
            err_min = Function('ri.err_min', IntSort(), RealSort())
            #large_value = Function('ri.large_value', IntSort(), RealSort())
            large_value = Real('ri.large_value')

        ps_prev = [(0,0)] * len(precs)

        decls={ 'ri.max_value':max_value,
                #'ri.normal_bound':normal_bound,
                'ri.err_denom':err_denom,
                'ri.err_min':err_min,
                'ri.large_value':large_value }
    
        ast = parse_smt2_file(smt2_file, decls=decls)
        
        # max_value is not approximated; Set the target value.
        for i in range(len(precs)):
            eb, sb = precs[i]
        
            emax = 2**(eb-1)-1
        
            max_value_v = (2**sb-1) * 2**(emax-sb+1)
            if not len(precs) >= 2:
                solver.add( parse_smt2_string(
                    '(assert (= ri.max_value %d.))' % max_value_v, decls=decls) )
                solver.add( parse_smt2_string(
                    '(assert (> ri.large_value (* 2 ri.max_value)))', decls=decls) )
            else:
                solver.add( parse_smt2_string(
                    '(assert (= (ri.max_value %d) %d.))' % (i, max_value_v), decls=decls) )
                solver.add( parse_smt2_string(
                    '(assert (> ri.large_value (* 2 (ri.max_value %d))))' % i, decls=decls) )

    if args.pset == 0:
        prec_set = [(11,53)]
    elif args.pset == 1:
        prec_set = [(4,4), (5,11), (8,24), (11,53), (15,113)]

    #t_start = time.time()
    
    etime = 0.0
    mem = -1.0
    for (eb, sb) in prec_set:
        if args.timeout < float('Inf'):
            to = int((args.timeout-etime)*1000)
            if 0 < to:
                solver.set('timeout', to)
    
        if args.pset > 0:
            solver.push()
    
            if not assert_rint_constants(solver, decls, precs, ps_prev, eb, sb):
                # if precision cannot be improved, terminate.
                break
    
        solver.add(ast)

        res = solver.check()
        #print('solve w/ (%d,%d): %s' % (eb, sb, res))
        #print(solver.statistics())
        
        st = solver.statistics()
        #rtime -= min(int(st.get_key_value('time')), rtime)
        if 'time' in st.keys():
            etime += st.get_key_value('time')
        if args.timeout - etime <= 0:
            res = 'timeout'

        if 'memory' in st.keys():
            #print("memory: %f" % st.get_key_value('memory'))
            m = st.get_key_value('memory')
            if m > mem:
                mem = m
        if (is_dplus and res == sat) or (not is_dplus and res == unsat) or res == 'timeout':
            #print("%s (%d;%d)" % (res, eb, sb))
            res = "%s (%d;%d)" % (res, eb, sb)
            #print(solver.statistics())
            #print("time: %f" % etime)
            #t_end = time.time()
            #print("tt: %f" % (t_end - t_start))
    
            #quit()
            queue.put((res, etime, mem))
            return

        if args.pset > 0:
            solver.pop()

    queue.put(('unknown', etime, mem))
    return

#

if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        usage="%(prog)s [OPTION] [SMT2_DM_FILE] [SMT2_DP_FILE]...",
        description="Translate Real exprs into other exprs and print the content."
    )
    parser.add_argument(
        "-v", "--version", action="version",
        version = f"{parser.prog} version 0.0.1" )
    parser.add_argument(
        "-t", "--timeout", nargs='?', type=float, default=float('Inf') )
    
    parser.add_argument(
        "--pset", nargs='?', type=int, default=1 )
    
    parser.add_argument("smt2_dm_file", nargs=1)
    parser.add_argument("smt2_dp_file", nargs=1)
    args = parser.parse_args()

    smt2_dp_file = args.smt2_dp_file[0]
    assert os.path.exists(smt2_dp_file)
    smt2_dm_file = args.smt2_dm_file[0]
    assert os.path.exists(smt2_dm_file)
    
    # Load the precisions info.
    precs = []
    f = open(smt2_dp_file, 'r')
    for l in f:
        ts = re.split(r',\s|;*\s', l)
        if len(ts) >= 4 and ts[1][0] == 'p':
            if int(ts[2]) == 0 and int(ts[3]) == 0:
                print('error in translation')
                print('time: 0')
                print('memory: 0')
                f.close()
                quit()

            precs.append((int(ts[2]), int(ts[3])))
        else:
            break
    f.close()

    #solve(args)

    #mp.set_start_method('spawn')
    #p_conn, c_conn = mp.Pipe()
    queue = mp.Queue()
    p1 = mp.Process(target=solve, args=(queue, args, precs, smt2_dm_file, False))
    p2 = mp.Process(target=solve, args=(queue, args, precs, smt2_dp_file, True))
    p1.start()
    p2.start()
    #p1.join()
    #p2.join()
    #p_conn.close()

    res = queue.get()
    mem = res[2]
    if len(res) < 3 or res[0][0:3] != "sat" and res[0][0:3] != "uns":
        res = queue.get()
        if mem < res[2]:
            mem = res[2]

    print(res[0])
    print('time: %f' % res[1])
    print('memory: %f' % mem)

    p1.kill()
    p2.kill()
   
# eof
