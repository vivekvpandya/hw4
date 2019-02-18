package submit;

import java.util.*;
import joeq.Class.jq_Class;
import joeq.Main.Helper;
import joeq.Compiler.Quad.*;
import joeq.Compiler.Quad.Operand.*;
import flow.Flow;

public class Optimize {
    

public static class NullCheckObject implements Flow.DataflowObject {
	private Set<String> set;
	public static Set<String> universalSet;
        public void setToTop() {
		set = new TreeSet<String>();
        }
        public void setToBottom() {
		set = new TreeSet<String>(universalSet);
        }
        public void meetWith (Flow.DataflowObject o) {
            NullCheckObject a = (NullCheckObject)o;
	        set.retainAll(a.set);
        }
        public void copy (Flow.DataflowObject o) {
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

public static class Pair implements Comparable<Pair>  {
	private String ref;
	private String index;
	public void setRef(String r) {  ref = r;}
	public void setIndex(String i) { index = i;}
	public String getRef() { return ref;}
	public String getIndex() {return index;}
	public Pair(String r, String i) { ref = r; index = i;};
	@Override 
	public String toString() {
		return ref+index;
	}
	@Override
	public int hashCode() {
		return toString().hashCode();
	}
	@Override
	public boolean equals(Object other) {
	if (!(other instanceof Pair))
		return false;
	Pair otherPair = (Pair) other;
	return ref == otherPair.getRef() && index == otherPair.getIndex();
	}
	public int compareTo(Pair other) {
		String val = toString();
		return val.compareTo(other.toString());
	}
}

public static class BoundsCheckObject implements Flow.DataflowObject {
	private Set<Pair> set;
	public static Set<Pair> universalSet;
        public void setToTop() {
		set = new TreeSet<Pair>();
        }
        public void setToBottom() {
		set = new TreeSet<Pair>(universalSet);
        }
        public void meetWith (Flow.DataflowObject o) {
            BoundsCheckObject a = (BoundsCheckObject)o;
	    set.retainAll(a.set);
        }
        public void copy (Flow.DataflowObject o) {
            BoundsCheckObject a = (BoundsCheckObject)o;
		set = new TreeSet<Pair>(a.set);
        }

	public boolean contains(String ref, String index) {
		Pair obj = new Pair(ref, index);
		return set.contains(obj);
	}

        public BoundsCheckObject() {
		set = new TreeSet<Pair>();
        }

	@Override
	public boolean equals(Object o)
	{
		if (o instanceof BoundsCheckObject) {
			BoundsCheckObject a = (BoundsCheckObject) o;
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

	public void genVar(String k, String v) {set.add(new Pair(k,v));}
	public void killVar(String val)  {
		Iterator<Pair> it = set.iterator();
		while(it.hasNext()) {
			Pair pair = it.next();
			if (pair.getRef() == val || pair.getIndex() == val)
				set.remove(pair);
		}
	}
        /* Also, freshly constructed objects should be Top, equals
         * must be looser than object identity, and toString should
         * return things in a form that's repeatable across runs.  Use
         * SortedSets and SortedMaps instead of the normal kinds.
         */
    }

    public static class NullCheckOpt implements Flow.Analysis {
	private NullCheckObject[] in, out;
	private NullCheckObject entry, exit;
        /* Analysis-specific customization.  You can use these to
         * precompute values or output results, if you wish. */

        public void preprocess (ControlFlowGraph cfg) {
		
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
        }
        public void postprocess (ControlFlowGraph cfg) {
	
	QuadIterator qit = new QuadIterator(cfg);
	while (qit.hasNext()) {
		Quad q = qit.next();
		int x = q.getID();
		if (q.getOperator() instanceof Operator.NullCheck) {
		for (RegisterOperand use: q.getUsedRegisters()) {
			if (in[x].contains(use.getRegister().toString())) {
				qit.remove();
				break;
			}

		}
		}
	}
	}

        /* Is this a forward dataflow analysis? */
        public boolean isForward () { return true;}

        /* Routines for interacting with dataflow values.  You may
         * assume that the quad passed in is part of the relevant
         * CFG. */

        /**
         * Returns the entry value
         **/
       public  Flow.DataflowObject getEntry() {
		
		NullCheckObject o = new NullCheckObject();
		o.copy(entry);
		return o;
	}
        /**
         * Returns the exit value
         **/
        public Flow.DataflowObject getExit() { 
		
		NullCheckObject o = new NullCheckObject();
		o.copy(exit);
		return o;
	}		
        /**
        /**
         * Sets the entry value
         **/
        public void setEntry(Flow.DataflowObject value) {
	entry.copy(value);		
        }
        /**
         * Sets the exit value
         **/
        public void setExit(Flow.DataflowObject value) {
	exit.copy(value);
        }
        /**
         * Returns the IN value of a quad
         **/
        public Flow.DataflowObject getIn(Quad q) {
	NullCheckObject r = new NullCheckObject();
	r.copy(in[q.getID()]);
	return r;
	}
        /**
         * Returns the OUT value of a quad
         **/	
        public Flow.DataflowObject getOut(Quad q) {
		NullCheckObject r = new NullCheckObject();
		r.copy(out[q.getID()]);
		return r;
	}
        /**
         * Sets the IN value of a quad
         **/
        public void setIn(Quad q, Flow.DataflowObject value) {
		in[q.getID()].copy(value);
        }
        /**
         * Sets the OUT value of a quad
         **/
        public void setOut(Quad q, Flow.DataflowObject value) {
		out[q.getID()].copy(value);
        }

        /**
         * Returns a new DataflowObject of the same type
         **/
        public Flow.DataflowObject newTempVar() {
		NullCheckObject d = new NullCheckObject();
		d.setToBottom();
		return d;
	}

        /**
         * Actually performs the transfer operation on the given
         * quad.
         **/
        public void processQuad(Quad q) {
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

    public static class BoundsCheckOpt implements Flow.Analysis {
	private BoundsCheckObject[] in, out;
	private BoundsCheckObject entry, exit;
        /* Analysis-specific customization.  You can use these to
         * precompute values or output results, if you wish. */

        public void preprocess (ControlFlowGraph cfg) {
		
        QuadIterator qit = new QuadIterator(cfg);
        int max = 0;
        while (qit.hasNext()) {
            int x = qit.next().getID();
            if (x > max) max = x;
        }
        max += 1;
        in = new BoundsCheckObject[max];
        out = new BoundsCheckObject[max];
        qit = new QuadIterator(cfg);

        Set<Pair> s = new TreeSet<Pair>();
        BoundsCheckObject.universalSet = s;

        while (qit.hasNext()) {
			
            Quad q = qit.next();
	    if (q.getOperator() instanceof Operator.BoundsCheck) {
	    	s.add(new Pair(Operator.BoundsCheck.getRef(q).toString(), Operator.BoundsCheck.getIndex(q).toString()));
	    }
        }

        entry = new BoundsCheckObject();
        exit = new BoundsCheckObject();
        for (int i=0; i<in.length; i++) {
            in[i] = new BoundsCheckObject();
            out[i] = new BoundsCheckObject();
	        out[i].setToBottom();
        }
        }
        public void postprocess (ControlFlowGraph cfg) {
	
		
	QuadIterator qit = new QuadIterator(cfg);
	while (qit.hasNext()) {
		Quad q = qit.next();
		int x = q.getID();
		if (q.getOperator() instanceof Operator.BoundsCheck) {
		String ref = Operator.BoundsCheck.getRef(q).toString();
		String index = Operator.BoundsCheck.getIndex(q).toString();
		if (in[x].contains(ref, index)) {
				qit.remove();
		}

		}
	}
	}

        /* Is this a forward dataflow analysis? */
        public boolean isForward () { return true;}

        /* Routines for interacting with dataflow values.  You may
         * assume that the quad passed in is part of the relevant
         * CFG. */

        /**
         * Returns the entry value
         **/
       public  Flow.DataflowObject getEntry() {
		
	BoundsCheckObject o = new BoundsCheckObject();
		o.copy(entry);
		return o;
	}
        /**
         * Returns the exit value
         **/
        public Flow.DataflowObject getExit() { 
		
		BoundsCheckObject o = new BoundsCheckObject();
		o.copy(exit);
		return o;
	}		
        /**
        /**
         * Sets the entry value
         **/
        public void setEntry(Flow.DataflowObject value) {
	entry.copy(value);		
        }
        /**
         * Sets the exit value
         **/
        public void setExit(Flow.DataflowObject value) {
	exit.copy(value);
        }
        /**
         * Returns the IN value of a quad
         **/
        public Flow.DataflowObject getIn(Quad q) {
	BoundsCheckObject r = new BoundsCheckObject();
	r.copy(in[q.getID()]);
	return r;
	}
        /**
         * Returns the OUT value of a quad
         **/	
        public Flow.DataflowObject getOut(Quad q) {
		BoundsCheckObject r = new BoundsCheckObject();
		r.copy(out[q.getID()]);
		return r;
	}
        /**
         * Sets the IN value of a quad
         **/
        public void setIn(Quad q, Flow.DataflowObject value) {
		in[q.getID()].copy(value);
        }
        /**
         * Sets the OUT value of a quad
         **/
        public void setOut(Quad q, Flow.DataflowObject value) {
		out[q.getID()].copy(value);
        }

        /**
         * Returns a new DataflowObject of the same type
         **/
        public Flow.DataflowObject newTempVar() {
		BoundsCheckObject d = new BoundsCheckObject();
		d.setToBottom();
		return d;
	}

        /**
         * Actually performs the transfer operation on the given
         * quad.
         **/
        public void processQuad(Quad q) {
		BoundsCheckObject d = new BoundsCheckObject();
		d.copy(in[q.getID()]);
		for (RegisterOperand def : q.getDefinedRegisters()) {
			d.killVar(def.getRegister().toString());
		}
		if (q.getOperator() instanceof Operator.BoundsCheck) {
			d.genVar(Operator.BoundsCheck.getRef(q).toString(), Operator.BoundsCheck.getIndex(q).toString());
		}
		out[q.getID()].copy(d);
        }
    }

    public static class Solver implements ControlFlowGraphVisitor {
        protected Flow.Analysis analysis;
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
        private Flow.DataflowObject computeConfluence(Iterator<Quad> quads, boolean direction)
        {
            Flow.DataflowObject temp = analysis.newTempVar();
            while(quads.hasNext())
            {
                Quad P = (Quad)quads.next();
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
            Flow.DataflowObject original, modified;
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
                    Iterator<Quad> pre = iter.predecessors();
                    analysis.setIn(quad, computeConfluence(pre, true) );
                    if(transfer(quad, true))
                        changesMade = true;

                    // Check if we need to update the exit
                    if(containsEntryOrExit(iter.successors()))
                    {
                        Flow.DataflowObject temp = analysis.getExit();
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
                        Flow.DataflowObject temp = analysis.getEntry();
                        temp.meetWith(analysis.getIn(quad));
                        analysis.setEntry(temp);
                    }
                }
            }
        }
        // this needs to come last.
        analysis.postprocess(cfg);
        }
        void registerAnalysis(Flow.Analysis a) {
            this.analysis = a;
        }
    }
	
     /*
     * optimizeFiles is a list of names of class that should be optimized
     * if nullCheckOnly is true, disable all optimizations except "remove redundant NULL_CHECKs."
     */
    public static void optimize(List<String> optimizeFiles, boolean nullCheckOnly) {
	Solver solver = new Solver();
	Flow.Analysis analysis = new NullCheckOpt();
	solver.registerAnalysis(analysis);
	Solver solver1 = new Solver();
	Flow.Analysis boundsCheck = new BoundsCheckOpt();
	solver1.registerAnalysis(boundsCheck);
	
        /*Flow.Solver flowSolver;

        try {
            Object solver_obj = Class.forName(solver_name).newInstance();
            solver = (Solver) solver_obj;
        } catch (Exception ex) {
            System.out.println("ERROR: Could not load class '" + solver_name +
                "' as Solver: " + ex.toString());
            System.out.println(usage);
            return;
        }*/

	/*Flow.Analysis ConstantProp;
	try {
		Object analysisObj = Class.forName("flow.ConstantProp").newInstance();
		ConstantProp = (Flow.Analysis) analysisObj;
	} catch (Exception e) {
		System.out.println(e.toString());
		return;
	}*/
	//solver1.registerAnalysis(ConstantProp);
	for (int i = 0; i < optimizeFiles.size(); i++) {
            jq_Class classes = (jq_Class)Helper.load(optimizeFiles.get(i));
            // Run your optimization on each classes.
            Helper.runPass(classes, solver);
	    if (!nullCheckOnly) {
	    	Helper.runPass(classes, solver1);
	    }
	}
    }
}
