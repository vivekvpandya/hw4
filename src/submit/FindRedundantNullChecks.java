package submit;

import joeq.Class.jq_Class;
import joeq.Main.Helper;
import joeq.Compiler.Quad.*;
import java.util.*;
import joeq.Compiler.Quad.Operand.*;

public class FindRedundantNullChecks {
public static class DataflowObject {
	private Set<String> set;
	public static Set<String> universalSet;
        void setToTop() {
		set = new TreeSet<String>();
        }
        void setToBottom() {
		set = new TreeSet<String>(universalSet);
        }
        void meetWith (DataflowObject o) {
	set.retainAll(o.set);

        }
        void copy (DataflowObject o) {
		set = new TreeSet<String>(o.set);
        }

	public boolean contains(String v) {
		return set.contains(v);
	}

        public DataflowObject() {
		set = new TreeSet<String>();
        }

	@Override
	public boolean equals(Object o)
	{
		if (o instanceof DataflowObject) {
			DataflowObject a = (DataflowObject) o;
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

    public static class Analysis {
	private DataflowObject[] in, out;
	private DataflowObject entry, exit;
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
        in = new DataflowObject[max];
        out = new DataflowObject[max];
        qit = new QuadIterator(cfg);

        Set<String> s = new TreeSet<String>();
        DataflowObject.universalSet = s;

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

        entry = new DataflowObject();
        exit = new DataflowObject();
        for (int i=0; i<in.length; i++) {
            in[i] = new DataflowObject();
            out[i] = new DataflowObject();
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
		
	System.out.print(cfg.getMethod().getName().toString());	
	QuadIterator qit = new QuadIterator(cfg, true);
	TreeSet<Integer> tSet = new TreeSet<Integer>();
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
				tSet.add(x);
				break;
			}

		}
		}
	}
        Iterator<Integer> itr =  tSet.iterator();
	if (itr.hasNext())
		System.out.print(' ');
	while (itr.hasNext()) {
		System.out.print(itr.next());
		if (itr.hasNext())
			System.out.print(' ');
	}
	System.out.print('\n');
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
		
		DataflowObject o = new DataflowObject();
		o.copy(entry);
		return o;
	}
        /**
         * Returns the exit value
         **/
        DataflowObject getExit() { 
		
		DataflowObject o = new DataflowObject();
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
	DataflowObject r = new DataflowObject();
	r.copy(in[q.getID()]);
	return r;
	}
        /**
         * Returns the OUT value of a quad
         **/	
        DataflowObject getOut(Quad q) {
		DataflowObject r = new DataflowObject();
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
		DataflowObject d = new DataflowObject();
		d.setToBottom();
		return d;
	}

        /**
         * Actually performs the transfer operation on the given
         * quad.
         **/
        void processQuad(Quad q) {
		DataflowObject d = new DataflowObject();
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
     * args is an array of class names
     * method should print out a list of quad ids of redundant null checks
     * for each function as described on the course webpage
     */
    public static void main(String[] args) {
        Solver solver =  new Solver();
        Analysis analysis = new Analysis();

	//for (int i =0; i < args.length; ++i)
		//System.out.println(args[i]);
          // get the classes we will be visiting.
        jq_Class[] classes = new jq_Class[args.length];
        for (int i=0; i < classes.length; i++)
            classes[i] = (jq_Class)Helper.load(args[i]);

        // register the analysis with the solver.
        solver.registerAnalysis(analysis);

        // visit each of the specified classes with the solver.
        for (int i=0; i < classes.length; i++) {
	    //System.out.println("Now analyzing " + classes[i].getName());
            Helper.runPass(classes[i], solver);
        }
    }
}
