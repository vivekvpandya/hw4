package submit;

import java.util.*;
import joeq.Class.jq_Class;
import joeq.Main.Helper;
import joeq.Compiler.Quad.*;
import joeq.Compiler.Quad.Operand.*;

public class Optimize {
    
        public static interface DataflowObject {
        void setToTop();
        void setToBottom();
        void meetWith (DataflowObject o);
        void copy (DataflowObject o);

        /* Also, freshly constructed objects should be Top, equals
         * must be looser than object identity, and toString should
         * return things in a form that's repeatable across runs.  Use
         * SortedSets and SortedMaps instead of the normal kinds.
         */
    }

    public static interface Analysis {

        /* Analysis-specific customization.  You can use these to
         * precompute values or output results, if you wish. */

        void preprocess (ControlFlowGraph cfg);
        void postprocess (ControlFlowGraph cfg);

        /* Is this a forward dataflow analysis? */
        boolean isForward ();

        /* Routines for interacting with dataflow values.  You may
         * assume that the quad passed in is part of the relevant
         * CFG. */

        /**
         * Returns the entry value
         **/
        DataflowObject getEntry();
        /**
         * Returns the exit value
         **/
        DataflowObject getExit();
        /**
         * Sets the entry value
         **/
        void setEntry(DataflowObject value);
        /**
         * Sets the exit value
         **/
        void setExit(DataflowObject value);	
        /**
         * Returns the IN value of a quad
         **/
        DataflowObject getIn(Quad q);
        /**
         * Returns the OUT value of a quad
         **/	
        DataflowObject getOut(Quad q);
        /**
         * Sets the IN value of a quad
         **/
        void setIn(Quad q, DataflowObject value);
        /**
         * Sets the OUT value of a quad
         **/
        void setOut(Quad q, DataflowObject value);

        /**
         * Returns a new DataflowObject of the same type
         **/
        DataflowObject newTempVar();

        /**
         * Actually performs the transfer operation on the given
         * quad.
         **/
        void processQuad(Quad q);
    }

public static class NullCheckObject implements DataflowObject {
	private Set<String> set;
	public static Set<String> universalSet;
        void setToTop() {
		set = new TreeSet<String>();
        }
        void setToBottom() {
		set = new TreeSet<String>(universalSet);
        }
        void meetWith (DataflowObject o) {
            NullCheckObject a = (NullCheckObject)o;
	        set.retainAll(a.set);
        }
        void copy (DataflowObject o) {
            NullCheckObject a = (NullCheckObject)o;
		set = new TreeSet<String>(a.set);
        }

	public boolean contains(String v) {
		return set.contains(v);
	}

        public NullCheckObject() {
		set = new TreeSet<String>();
        }

	@Override
	public boolean equals(Object o)
	{
		if (o instanceof NullCheckObject) {
			NullCheckObject a = (NullCheckObject) o;
			return set.equals(a.set);
		}
		return false;
	}
	@Override
	public int hashCode() {
		return set.hashCode();
	}

	@Override
	public String toString() {
		return set.toString();
	}

	public void genVar(String v) {set.add(v);}
	public void killVar(String v) {set.remove(v);}
        /* Also, freshly constructed objects should be Top, equals
         * must be looser than object identity, and toString should
         * return things in a form that's repeatable across runs.  Use
         * SortedSets and SortedMaps instead of the normal kinds.
         */
    }

    public static class NullCheckOpt implements Analysis {
	private NullCheckObject[] in, out;
	private NullCheckObject entry, exit;
        /* Analysis-specific customization.  You can use these to
         * precompute values or output results, if you wish. */

        void preprocess (ControlFlowGraph cfg) {
		
  //      System.out.println("Method: "+cfg.getMethod().getName().toString());
        /* Generate initial conditions. */
        QuadIterator qit = new QuadIterator(cfg);
        int max = 0;
        while (qit.hasNext()) {
            int x = qit.next().getID();
            if (x > max) max = x;
        }
        max += 1;
        in = new NullCheckObject[max];
        out = new NullCheckObject[max];
        qit = new QuadIterator(cfg);

        Set<String> s = new TreeSet<String>();
        NullCheckObject.universalSet = s;

        /* Not sure if  Arguments are always there. */
        int numargs = cfg.getMethod().getParamTypes().length;
        for (int i = 0; i < numargs; i++) {
            s.add("R"+i);
        }

        while (qit.hasNext()) {
            Quad q = qit.next();
            for (RegisterOperand def : q.getDefinedRegisters()) {
                s.add(def.getRegister().toString());
            }
            for (RegisterOperand use : q.getUsedRegisters()) {
                s.add(use.getRegister().toString());
            }
        }

        entry = new NullCheckObject();
        exit = new NullCheckObject();
        for (int i=0; i<in.length; i++) {
            in[i] = new NullCheckObject();
            out[i] = new NullCheckObject();
	        out[i].setToBottom();
        }
//	System.out.println("Initialization completed.");
        }
        void postprocess (ControlFlowGraph cfg) {
	
        /*System.out.println("entry: "+entry.toString());
        for (int i=1; i<in.length; i++) {
            System.out.println(i+" in:  "+in[i].toString());
            System.out.println(i+" out: "+out[i].toString());
        }*/
		
	//System.out.print(cfg.getMethod().getName().toString());	
	QuadIterator qit = new QuadIterator(cfg, true);
	//TreeSet<Integer> tSet = new TreeSet<Integer>();
	while (qit.hasNext()) {
		Quad q = qit.next();
		int x = q.getID();
		if (q.getOperator() instanceof Operator.NullCheck) {
		//System.out.println(q);
		//System.out.println("Preds: ");
		//Iterator<Quad> pred =  qit.predecessors();
		//while (pred.hasNext()) {
		//	System.out.println("\t" + pred.next().toString());
		//}
		for (RegisterOperand use: q.getUsedRegisters()) {
			if (in[x].contains(use.getRegister().toString())) {
				//tSet.add(x);
				qit.remove();
				break;
			}

		}
		}
	}
        /*Iterator<Integer> itr =  tSet.iterator();
	if (itr.hasNext())
		System.out.print(' ');
	while (itr.hasNext()) {
		System.out.print(itr.next());
		if (itr.hasNext())
			System.out.print(' ');
	}
	System.out.print('\n');*/
	}

        /* Is this a forward dataflow analysis? */
        boolean isForward () { return true;}

        /* Routines for interacting with dataflow values.  You may
         * assume that the quad passed in is part of the relevant
         * CFG. */

        /**
         * Returns the entry value
         **/
        DataflowObject getEntry() {
		
		NullCheckObject o = new NullCheckObject();
		o.copy(entry);
		return o;
	}
        /**
         * Returns the exit value
         **/
        DataflowObject getExit() { 
		
		NullCheckObject o = new NullCheckObject();
		o.copy(exit);
		return o;
	}		
        /**
        /**
         * Sets the entry value
         **/
        void setEntry(DataflowObject value) {
	entry.copy(value);		
        }
        /**
         * Sets the exit value
         **/
        void setExit(DataflowObject value) {
	exit.copy(value);
        }
        /**
         * Returns the IN value of a quad
         **/
        DataflowObject getIn(Quad q) {
	NullCheckObject r = new NullCheckObject();
	r.copy(in[q.getID()]);
	return r;
	}
        /**
         * Returns the OUT value of a quad
         **/	
        DataflowObject getOut(Quad q) {
		NullCheckObject r = new NullCheckObject();
		r.copy(out[q.getID()]);
		return r;
	}
        /**
         * Sets the IN value of a quad
         **/
        void setIn(Quad q, DataflowObject value) {
		in[q.getID()].copy(value);
        }
        /**
         * Sets the OUT value of a quad
         **/
        void setOut(Quad q, DataflowObject value) {
		out[q.getID()].copy(value);
        }

        /**
         * Returns a new DataflowObject of the same type
         **/
        DataflowObject newTempVar() {
		NullCheckObject d = new NullCheckObject();
		d.setToBottom();
		return d;
	}

        /**
         * Actually performs the transfer operation on the given
         * quad.
         **/
        void processQuad(Quad q) {
		NullCheckObject d = new NullCheckObject();
		d.copy(in[q.getID()]);
		for (RegisterOperand def : q.getDefinedRegisters()) {
			d.killVar(def.getRegister().toString());
		}
		if (q.getOperator() instanceof Operator.NullCheck) {
		for (RegisterOperand use: q.getUsedRegisters()) {
			d.genVar(use.getRegister().toString());
		}
		}
		out[q.getID()].copy(d);
        }
    }


    public static class Solver implements ControlFlowGraphVisitor {
        protected Analysis analysis;
        private boolean containsEntryOrExit(Iterator<Quad> quads)
        {
            while(quads.hasNext())
            {
                Quad P = (Quad)quads.next();
                if(P==null)
                    return true;
            }
            return false;
        }
    
        /**
         * Computes the meet over all predecessors/successors
         */
        private DataflowObject computeConfluence(Iterator<Quad> quads, boolean direction)
        {
            DataflowObject temp = analysis.newTempVar();
            while(quads.hasNext())
            {
                Quad P = (Quad)quads.next();
		//System.out.println("\t"+P);
                if(P!=null)
                {
                    if(direction)
                        temp.meetWith( analysis.getOut(P) );
                    else
                        temp.meetWith( analysis.getIn(P) );
                }
                else
                {
                    if(direction)
                        temp.meetWith( analysis.getEntry() );
                    else
                        temp.meetWith( analysis.getExit() );
                }
            }
            return temp;
        }
        /**
         * Processes a quad in the specified direction.
         * Return value is true if changes were made
         */
        private boolean transfer(Quad quad, boolean direction)
        {
            DataflowObject original, modified;
            if(direction)
                original = analysis.getOut(quad);
            else
                original = analysis.getIn(quad);
            analysis.processQuad(quad);
    
            if(direction)
                modified = analysis.getOut(quad);
            else
                modified = analysis.getIn(quad);
    
            return !modified.equals(original);
        }

        public void visitCFG(ControlFlowGraph cfg) {
            // this needs to come first.
        analysis.preprocess(cfg);
        boolean changesMade = true;
        while(changesMade)
        {
            changesMade = false;
            QuadIterator iter = new QuadIterator(cfg, analysis.isForward() );
            if(analysis.isForward())
            {
                while(iter.hasNext()) // Iterate forward
                {
                    Quad quad = (Quad)iter.next();
		    //System.out.println(quad);
		    //System.out.println("Preds: ");
                    Iterator<Quad> pre = iter.predecessors();
                    analysis.setIn(quad, computeConfluence(pre, true) );
                    if(transfer(quad, true))
                        changesMade = true;

                    // Check if we need to update the exit
                    if(containsEntryOrExit(iter.successors()))
                    {
                        DataflowObject temp = analysis.getExit();
                        temp.meetWith(analysis.getOut(quad));
                        analysis.setExit(temp);
                    }
                }
            }
            else
            {
                while(iter.hasPrevious()) // Iterate backward
                {
                    Quad quad = (Quad)iter.previous();
                    Iterator<Quad> pre = iter.successors();
                    analysis.setOut(quad, computeConfluence(pre, false ) );
                    if(transfer(quad, false))
                        changesMade = true;

                    // Check if we need to update the entry
                    if(containsEntryOrExit(iter.predecessors()))
                    {
                        DataflowObject temp = analysis.getEntry();
                        temp.meetWith(analysis.getIn(quad));
                        analysis.setEntry(temp);
                    }
                }
            }
        }
        // this needs to come last.
        analysis.postprocess(cfg);
        }
        void registerAnalysis(Analysis a) {
            this.analysis = a;
        }
    }
	
     /*
     * optimizeFiles is a list of names of class that should be optimized
     * if nullCheckOnly is true, disable all optimizations except "remove redundant NULL_CHECKs."
     */
    public static void optimize(List<String> optimizeFiles, boolean nullCheckOnly) {
	Solver solver = new Solver();
	Analysis analysis = new NullCheckOpt();
	solver.registerAnalysis(analysis);
	for (int i = 0; i < optimizeFiles.size(); i++) {
            jq_Class classes = (jq_Class)Helper.load(optimizeFiles.get(i));
            // Run your optimization on each classes.
            Helper.runPass(classes, solver);
	}
    }
}
