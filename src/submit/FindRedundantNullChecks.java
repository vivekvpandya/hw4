package submit;

import joeq.Class.jq_Class;
import joeq.Main.Helper;
import joeq.Compiler.Quad.*;
import java.util.*;
import joeq.Compiler.Quad.Operand.*;

public class FindRedundantNullChecks {
public class DataflowObject {
        void setToTop() {

        }
        void setToBottom() {

        }
        void meetWith (DataflowObject o) {

        }
        void copy (DataflowObject o) {

        }

        public DataflowObject() {

        }
        /* Also, freshly constructed objects should be Top, equals
         * must be looser than object identity, and toString should
         * return things in a form that's repeatable across runs.  Use
         * SortedSets and SortedMaps instead of the normal kinds.
         */
    }

    public class Analysis {

        /* Analysis-specific customization.  You can use these to
         * precompute values or output results, if you wish. */

        void preprocess (ControlFlowGraph cfg) {

        }
        void postprocess (ControlFlowGraph cfg) {

        }

        /* Is this a forward dataflow analysis? */
        boolean isForward () { return true;}

        /* Routines for interacting with dataflow values.  You may
         * assume that the quad passed in is part of the relevant
         * CFG. */

        /**
         * Returns the entry value
         **/
        DataflowObject getEntry() { return DataflowObject();}
        /**
         * Returns the exit value
         **/
        DataflowObject getExit() { return DataflowObject();}
        /**
         * Sets the entry value
         **/
        void setEntry(DataflowObject value) {

        }
        /**
         * Sets the exit value
         **/
        void setExit(DataflowObject value) {

        }
        /**
         * Returns the IN value of a quad
         **/
        DataflowObject getIn(Quad q) {return DataflowObject();}
        /**
         * Returns the OUT value of a quad
         **/	
        DataflowObject getOut(Quad q) { return DataflowObject();}
        /**
         * Sets the IN value of a quad
         **/
        void setIn(Quad q, DataflowObject value) {

        }
        /**
         * Sets the OUT value of a quad
         **/
        void setOut(Quad q, DataflowObject value) {

        }

        /**
         * Returns a new DataflowObject of the same type
         **/
        DataflowObject newTempVar() {return DataflowObject();}

        /**
         * Actually performs the transfer operation on the given
         * quad.
         **/
        void processQuad(Quad q) {

        }
    }

    public class Solver implements ControlFlowGraphVisitor {
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
            this.analysis = analyzer;
        }
    }

    /*
     * args is an array of class names
     * method should print out a list of quad ids of redundant null checks
     * for each function as described on the course webpage
     */
    public static void main(String[] args) {
        Solver solver;
        Analysis analysis;

          // get the classes we will be visiting.
        jq_Class[] classes = new jq_Class[args.length];
        for (int i=0; i < classes.length; i++)
            classes[i] = (jq_Class)Helper.load(args[i]);

        // register the analysis with the solver.
        solver.registerAnalysis(analysis);

        // visit each of the specified classes with the solver.
        for (int i=0; i < classes.length; i++) {
            System.out.println("Now analyzing " + classes[i].getName());
            Helper.runPass(classes[i], solver);
        }
    }
}
