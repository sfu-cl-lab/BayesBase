///////////////////////////////////////////////////////////////////////////////
// For information as to what this class does, see the Javadoc, below.       //
// Copyright (C) 1998, 1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006,       //
// 2007, 2008, 2009, 2010 by Peter Spirtes, Richard Scheines, Joseph Ramsey, //
// and Clark Glymour.                                                        //
//                                                                           //
// This program is free software; you can redistribute it and/or modify      //
// it under the terms of the GNU General Public License as published by      //
// the Free Software Foundation; either version 2 of the License, or         //
// (at your option) any later version.                                       //
//                                                                           //
// This program is distributed in the hope that it will be useful,           //
// but WITHOUT ANY WARRANTY; without even the implied warranty of            //
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the             //
// GNU General Public License for more details.                              //
//                                                                           //
// You should have received a copy of the GNU General Public License         //
// along with this program; if not, write to the Free Software               //
// Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA //
///////////////////////////////////////////////////////////////////////////////

package edu.cmu.tetrad.search;

import cern.colt.matrix.DoubleMatrix1D;
import cern.colt.matrix.DoubleMatrix2D;
import cern.colt.matrix.linalg.Algebra;
import edu.cmu.tetrad.data.*;
import edu.cmu.tetrad.graph.*;
import edu.cmu.tetrad.regression.RegressionDataset;
import edu.cmu.tetrad.util.*;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.text.NumberFormat;

/**
 * GesSearch is an implementation of the GES algorithm, as specified in Chickering (2002) "Optimal structure
 * identification with greedy search" Journal of Machine Learning Research. It works for both BayesNets and SEMs.
 * <p/>
 * Some code optimization could be done for the scoring part of the graph for discrete models (method scoreGraphChange).
 * Some of Andrew Moore's approaches for caching sufficient statistics, for instance.
 *
 * @author Ricardo Silva, Summer 2003
 * @author Joseph Ramsey, Revisions 10/2005
 */

public final class Ges3 implements GraphSearch, GraphScorer {

    /**
     * For formatting printed numbers.
     */
    private final NumberFormat nf = NumberFormatUtil.getInstance().getNumberFormat();
    /**
     * For linear algebra.
     */
    private final Algebra algebra = new Algebra();                        // s = vv * x, or s12 = Theta.1 * Theta.12
    SortedSet <Arrow> sortedArrows;
    Set <Arrow>[][] lookupArrows;
    SortedSet <Arrow> sortedArrowsBackwards;
    Set <Arrow>[][] lookupArrowsBackwards;
    double minJump = 0;
    /**
     * The data set, various variable subsets of which are to be scored.
     */
    private DataSet dataSet;
    /**
     * The covariance matrix for the data set.
     */
    private DoubleMatrix2D covariances;
    /**
     * Sample size, either from the data set or from the variances.
     */
    private int sampleSize;
    /**
     * Specification of forbidden and required edges.
     */
    private Knowledge knowledge = new Knowledge();
    /**
     * For discrete data scoring, the structure prior.
     */
    private double structurePrior;
    /**
     * For discrete data scoring, the sample prior.
     */
    private double samplePrior;

    /**
     * Caches scores for discrete search.
     */
    /** the call for localScoreCache replaced. @Diljot,@Chris
     * This is not used anymore in the program and has been replaced by the
     * scorehash function which is a hash that uses the score and the node names instead
     * the id's.
     *private final LocalScoreCache localScoreCache = new LocalScoreCache();
     */
    /**
     * Map from variables to their column indices in the data set.
     */
    private HashMap <Node, Integer> hashIndices;
    /**
     * Array of variable names from the data set, in order.
     */
    private String varNames[];
    /**
     * List of variables in the data set, in order.
     */
    private List <Node> variables;
    /**
     * True iff the data set is discrete.
     */
    private boolean discrete;
    /**
     * The true graph, if known. If this is provided, asterisks will be printed out next to false positive added edges
     * (that is, edges added that aren't adjacencies in the true graph).
     */
    private Graph trueGraph;
    /**
     * Elapsed time of the most recent search.
     */
    private long elapsedTime;
    /**
     * True if cycles are to be aggressively prevented. May be expensive for large graphs (but also useful for large
     * graphs).
     */
    private boolean aggressivelyPreventCycles = false;
    /**
     * Listeners for graph change events.
     */
    private transient List <PropertyChangeListener> listeners;
    /**
     * Penalty discount--the BIC penalty is multiplied by this (for continuous variables).
     */
    private double penaltyDiscount = 1.0;
    private boolean useFCutoff = false;
    private double fCutoffP = 0.01;
    /**
     * The maximum number of edges the algorithm will add to the graph.
     */
    private int maxEdgesAdded = -1;
    /**
     * The score for discrete searches.
     */
    private LocalDiscreteScore discreteScore;
    /**
     * The logger for this class. The config needs to be set.
     */
    private TetradLogger logger = TetradLogger.getInstance();
    /**
     * The top n graphs found by the algorithm, where n is <code>numPatternsToStore</code>.
     */
    private SortedSet <ScoredGraph> topGraphs = new TreeSet <ScoredGraph>();
    /**
     * The number of top patterns to store.
     */
    private int numPatternsToStore = 10;
    /**
     * Diljot,Chris :We are not going to use this scorehash from here since we want it to be global
     * and be able to reuse it between different calls, so we removed the declaration
     * from here and moved it to the BayesBaseH.java and then we pass that hashmap from there
     * to the functions here.
     */
    //Map<Node, Map<Set<Node>, Double>> globalScoreHash;
    private Map <Node, Integer> nodesHash;


    //===========================CONSTRUCTORS=============================//
    private boolean storeGraphs = true;
    private double minNeg = 0; //-1000000;

    //==========================PUBLIC METHODS==========================//
    private RegressionDataset regression;

    public Ges3(DataSet dataSet) {
        setDataSet(dataSet);
        if (dataSet != null) {
            setDiscreteScore(new BDeuScore(dataSet, 10, 1.0));
//            discreteScore = new MdluScore(dataSet, .001);
        }
        initialize(10., 0.001);
    }

    /**
     * Greedy equivalence search: Start from the empty graph, add edges till model is significant. Then start deleting
     * edges till a minimum is achieved.
     *
     * @return the resulting Pattern.
     */
    public Ges3(ICovarianceMatrix covMatrix) {
        setCovMatrix(covMatrix);
        if (dataSet != null) {
//            setDiscreteScore(new BDeuScore(dataSet, 10, .001));
            discreteScore = new MdluScore(dataSet, .001);
        }
        initialize(10., 1.0);
    }

    /**
     * Get all nodes that are connected to Y by an undirected edge and not adjacent to X.
     */
    private static List <Node> getTNeighbors(Node x, Node y, Graph graph) {
        List <Node> tNeighbors = graph.getAdjacentNodes(y);
        tNeighbors.removeAll(graph.getAdjacentNodes(x));

        for (int i = tNeighbors.size() - 1; i >= 0; i--) {
            Node z = tNeighbors.get(i);
            Edge edge = graph.getEdge(y, z);

            if (!Edges.isUndirectedEdge(edge)) {
                tNeighbors.remove(z);
            }
        }

        return tNeighbors;
    }

    /**
     * Get all nodes that are connected to Y by an undirected edge and adjacent to X
     */
    private static List <Node> getHNeighbors(Node x, Node y, Graph graph) {
        List <Node> hNeighbors = graph.getAdjacentNodes(y);
        hNeighbors.retainAll(graph.getAdjacentNodes(x));

        for (int i = hNeighbors.size() - 1; i >= 0; i--) {
            Node z = hNeighbors.get(i);
            Edge edge = graph.getEdge(y, z);

            if (!Edges.isUndirectedEdge(edge)) {
                hNeighbors.remove(z);
            }
        }

        return hNeighbors;
    }

    /**
     * Test if the candidate deletion is a valid operation (Theorem 17 from Chickering, 2002).
     */
    private static boolean validDelete(Set <Node> h, Set <Node> naXY, Graph graph) {
        Set <Node> set = new HashSet <Node>(naXY);
        set.removeAll(h);
        return isClique(set, graph);
    }

    /**
     * Find all nodes that are connected to Y by an undirected edge that are adjacent to X (that is, by undirected or
     * directed edge) NOTE: very inefficient implementation, since the current library does not allow access to the
     * adjacency list/matrix of the graph.
     */
    private static Set <Node> findNaYX(Node x, Node y, Graph graph) {
        Set <Node> naYX = new HashSet <Node>(graph.getAdjacentNodes(y));
        naYX.retainAll(graph.getAdjacentNodes(x));

        for (Node z : new HashSet <Node>(naYX)) {
            Edge edge = graph.getEdge(y, z);

            if (!Edges.isUndirectedEdge(edge)) {
                naYX.remove(z);
            }
        }

        return naYX;
    }

    /**
     * Returns true iif the given set forms a clique in the given graph.
     */
    private static boolean isClique(Set <Node> _nodes, Graph graph) {
        List <Node> nodes = new LinkedList <Node>(_nodes);
        for (int i = 0; i < nodes.size() - 1; i++) {
            for (int j = i + 1; j < nodes.size(); j++) {
                if (!graph.isAdjacentTo(nodes.get(i), nodes.get(j))) {
                    return false;
                }
            }
        }
        return true;
    }

    private static List <Set <Node>> powerSet(List <Node> nodes) {
        List <Set <Node>> subsets = new ArrayList <Set <Node>>();
        int total = (int) Math.pow(2, nodes.size());
        for (int i = 0; i < total; i++) {
            Set <Node> newSet = new HashSet <Node>();
            String selection = Integer.toBinaryString(i);

            int shift = nodes.size() - selection.length();

            for (int j = nodes.size() - 1; j >= 0; j--) {
                if (j >= shift && selection.charAt(j - shift) == '1') {
                    newSet.add(nodes.get(j));
                }
            }
            subsets.add(newSet);
        }

        return subsets;
    }

    private static int getRowIndex(int dim[], int[] values) {
        int rowIndex = 0;
        for (int i = 0; i < dim.length; i++) {
            rowIndex *= dim[i];
            rowIndex += values[i];
        }
        return rowIndex;
    }

    public boolean isAggressivelyPreventCycles() {
        return this.aggressivelyPreventCycles;
    }

    public void setAggressivelyPreventCycles(boolean aggressivelyPreventCycles) {
        this.aggressivelyPreventCycles = aggressivelyPreventCycles;
    }

    /**
     * Diljot&Chris :the function uses the global score hash from BayesBase.h. All the calls
     * to the scoring function ,forward search and backward search use this
     * globalScoreHash
     */
    public Graph search(Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        long startTime = System.currentTimeMillis();

        // Diljot,Chris :don't clear the hash as we want to reuse the old scores.
        // if(globalScoreHash != null)
        //	globalScoreHash.clear();

        // Check for missing values.
        if (covariances != null && DataUtils.containsMissingValue(covariances)) {
            throw new IllegalArgumentException(
                    "Please remove or impute missing values first.");
        }

        // Check for missing values.
        if (dataSet != null && DataUtils.containsMissingValue(dataSet)) {
            throw new IllegalArgumentException(
                    "Please remove or impute missing values first.");
        }


        Graph graph = new EdgeListGraph(new LinkedList <Node>(getVariables()));


        /**
         * Diljot,Chris :don't clear the hash as we want to reuse the old scores.
         * uncommenting the for loop would clear the score in each call to the tetrad and
         * thus fix all the problems in the structure of the bayesnet. Although after that
         * won't be any hits in the hash.
         */
        //globalScoreHash = new WeakHashMap<Node, Map<Set<Node>, Double>>();

        //   for (Node node : graph.getNodes()) {
        //       globalScoreHash.put(node, new HashMap<Set<Node>, Double>());
        // }

        fireGraphChange(graph);
        buildIndexing(graph);
        addRequiredEdges(graph);

        // Method 1-- original.

        // Don't need to score the original graph; the BIC scores all up to a constant.
        // double score = 0;

        /**
         * Using the globlScoreHash from BayesBase.h; will check if the score exists in hash,
         * else compute the score
         * same for the forward and the backward search parts
         */
        double score = scoreGraph(graph, globalScoreHash);

        storeGraph(new EdgeListGraph(graph), score);

        // Do forward search.
        score = fes(graph, score, globalScoreHash);

        // Do backward search.
        bes(graph, score, globalScoreHash);

//        score = fes(graph, score);
//        bes(graph, score);

        long endTime = System.currentTimeMillis();
        this.elapsedTime = endTime - startTime;
        this.logger.log("graph", "\nReturning this graph: " + graph);
        TetradLogger.getInstance().log("info", "Final Model BIC = " + nf.format(score));

        this.logger.log("info", "Elapsed time = " + (elapsedTime) / 1000. + " s");
        this.logger.flush();

//        return new ArrayList<ScoredGraph>(topGraphs).get(topGraphs.size() - 1).getGraph();

        return graph;

//        // Method 2-- Ricardo's tweak.
//        double score = scoreGraph(graph), newScore;
//
//        storeGraph(graph, score);
//
//        int iter = 0;
//        do {
//            newScore = fes(graph, score);
//            if (newScore > score) {
//                score = newScore;
//                newScore = bes(graph, score);
//
//                if (newScore > score) {
//                    score = newScore;
//                }
//                else {
//                    break;
//                }
//            }
//            else {
//                break;
//            }
//            //System.out.println("Current score = " + score);
//            iter++;
//        } while (iter < 100);
//
//        long endTime = System.currentTimeMillis();
//        this.elapsedTime = endTime - startTime;
//        this.logger.log("graph", "\nReturning this graph: " + graph);
//
//        this.logger.log("info", "Elapsed time = " + (elapsedTime) / 1000. + " s");
//        this.logger.flush();
//
//        return graph;
    }

    /**
     * Diljot,Chris:
     * search function uses the globalScoreCache; not clearing the the globalScoreHash
     * since we will be using the scores from the previous runs.
     */
    public Graph search(List <Node> nodes, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        long startTime = System.currentTimeMillis();

        //diljot,Chris: don't clear the hash
        // globalScoreHash.clear();

        if (!dataSet().getVariables().containsAll(nodes)) {
            throw new IllegalArgumentException(
                    "All of the nodes must be in " + "the supplied data set.");
        }

        Graph graph = new EdgeListGraph(nodes);
        buildIndexing(graph);
        addRequiredEdges(graph);
        double score = 0; //scoreGraph(graph);

        // Do forward search.
        // Use the globalScoreHash inside the function
        score = fes(graph, score, globalScoreHash);

        // Do backward search.
        // we need to pass the globalScoreHash to the bes.
        bes(graph, score, globalScoreHash);

        long endTime = System.currentTimeMillis();
        this.elapsedTime = endTime - startTime;

        this.logger.log("graph", "\nReturning this graph: " + graph);

        this.logger.log("info", "Elapsed time = " + (elapsedTime) / 1000. + " s");
        this.logger.flush();

        return graph;
    }

    public Knowledge getKnowledge() {
        return knowledge;
    }

    /**
     * Sets the background knowledge.
     *
     * @param knowledge the knowledge object, specifying forbidden and required edges.
     */
    public void setKnowledge(Knowledge knowledge) {
        if (knowledge == null) {
            throw new NullPointerException("Knowledge must not be null.");
        }
        this.knowledge = knowledge;
    }

    public long getElapsedTime() {
        return elapsedTime;
    }

    public void setElapsedTime(long elapsedTime) {
        this.elapsedTime = elapsedTime;
    }

    public void addPropertyChangeListener(PropertyChangeListener l) {
        getListeners().add(l);
    }

    public double getPenaltyDiscount() {
        return penaltyDiscount;
    }

    public void setPenaltyDiscount(double penaltyDiscount) {
        if (penaltyDiscount < 0) {
            throw new IllegalArgumentException("Penalty discount must be >= 0: "
                    + penaltyDiscount);
        }

        this.penaltyDiscount = penaltyDiscount;
    }

    public int getMaxEdgesAdded() {
        return maxEdgesAdded;
    }


    //===========================PRIVATE METHODS========================//

    public void setMaxEdgesAdded(int maxEdgesAdded) {
        if (maxEdgesAdded < -1) throw new IllegalArgumentException();

        this.maxEdgesAdded = maxEdgesAdded;
    }

    public void setTrueGraph(Graph trueGraph) {
        this.trueGraph = trueGraph;
    }

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    public double getScore(Graph dag, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        return scoreGraph(dag, globalScoreHash);
    }

    public SortedSet <ScoredGraph> getTopGraphs() {
        return topGraphs;
    }

    public int getNumPatternsToStore() {
        return numPatternsToStore;
    }

    public void setNumPatternsToStore(int numPatternsToStore) {
        if (numPatternsToStore < 1) {
            throw new IllegalArgumentException("Must store at least one pattern: " + numPatternsToStore);
        }

        this.numPatternsToStore = numPatternsToStore;
    }

    public boolean isStoreGraphs() {
        return storeGraphs;
    }

    public void setStoreGraphs(boolean storeGraphs) {
        this.storeGraphs = storeGraphs;
    }

    private void initialize(double samplePrior, double structurePrior) {
        setStructurePrior(structurePrior);
        setSamplePrior(samplePrior);
    }

    /**
     * Forward equivalence search.
     *
     * @param graph The graph in the state prior to the forward equivalence search.
     * @param score The score in the state prior to the forward equivalence search
     * @return the score in the state after the forward equivelance search. Note that the graph is changed as a
     * side-effect to its state after the forward equivelance search.
     */

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    private double fes(Graph graph, double score, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {

        List <Node> nodes = graph.getNodes();

        sortedArrows = new TreeSet <Arrow>();
        lookupArrows = new HashSet[nodes.size()][nodes.size()];

        nodesHash = new HashMap <Node, Integer>();
        int index = -1;

        for (Node node : nodes) {
            nodesHash.put(node, ++index);
        }

        TetradLogger.getInstance().log("info", "** FORWARD EQUIVALENCE SEARCH");
        TetradLogger.getInstance().log("info", "Initial Model BIC = " + nf.format(score));

        /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
        initializeArrowsForward(nodes, graph, globalScoreHash);

        while (!sortedArrows.isEmpty()) {
            Arrow arrow = sortedArrows.first();
            sortedArrows.remove(arrow);

            Node _x = nodes.get(arrow.getX());
            Node _y = nodes.get(arrow.getY());

            if (graph.isAdjacentTo(_x, _y)) {
                continue;
            }

            if (!findNaYX(_x, _y, graph).equals(arrow.getNaYX())) {
                /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
                reevaluateFoward(graph, nodes, arrow, globalScoreHash);
                continue;
            }

            if (!new HashSet <Node>(getTNeighbors(_x, _y, graph)).containsAll(arrow.getHOrT())) {
            	/* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
                reevaluateFoward(graph, nodes, arrow, globalScoreHash);
                continue;
            }

            if (!validInsert(_x, _y, arrow.getHOrT(), arrow.getNaYX(), graph)) {
                continue;
            }

            Node x = nodes.get(arrow.getX());
            Node y = nodes.get(arrow.getY());
            Set <Node> t = arrow.getHOrT();
            double bump = arrow.getBump();

            if (covariances != null && minJump == 0 && isUseFCutoff()) {
                double _p = getfCutoffP();
                double v;

                // Find the value for v that will yield p = _p

                for (v = 0.0; ; v += 0.25) {
                    int n = sampleSize();
                    double f = Math.exp((v - Math.log(n)) / n);
                    double p = 1 - ProbUtils.fCdf(f, n, n);

                    if (p <= _p) {
                        break;
                    }
                }

                minJump = v;
            }

            score = score + bump;
            insert(x, y, t, graph, score, true, bump);
            rebuildPattern(graph);

            storeGraph(graph, score);
            /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
            reevaluateFoward(graph, nodes, arrow, globalScoreHash);

            if (getMaxEdgesAdded() != -1 && graph.getNumEdges() >= getMaxEdgesAdded()) {
                break;
            }
        }

        return score;
    }

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    private double bes(Graph graph, double score, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        List <Node> nodes = graph.getNodes();

        TetradLogger.getInstance().log("info", "** BACKWARD EQUIVALENCE SEARCH");
        TetradLogger.getInstance().log("info", "Initial Model BIC = " + nf.format(score));
        /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
        initializeArrowsBackward(graph, globalScoreHash);

        while (!sortedArrowsBackwards.isEmpty()) {
            Arrow arrow = sortedArrowsBackwards.first();
            sortedArrowsBackwards.remove(arrow);

            Node _x = nodes.get(arrow.getX());
            Node _y = nodes.get(arrow.getY());

            if (!graph.isAdjacentTo(_x, _y)) {
                continue;
            }

            if (!findNaYX(_x, _y, graph).equals(arrow.getNaYX())) {
            	/* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
                reevaluateBackward(graph, nodes, arrow, globalScoreHash);
                continue;
            }

            if (!new HashSet <Node>(getHNeighbors(_x, _y, graph)).containsAll(arrow.getHOrT())) {
            	/* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
                reevaluateBackward(graph, nodes, arrow, globalScoreHash);
                continue;
            }

            if (!validDelete(arrow.getHOrT(), arrow.getNaYX(), graph)) {
                continue;
            }

            Node x = nodes.get(arrow.getX());
            Node y = nodes.get(arrow.getY());
            Set <Node> h = arrow.getHOrT();
            double bump = arrow.getBump();

            score = score + bump;
            delete(x, y, h, graph, score, true, bump);
            rebuildPattern(graph);

            storeGraph(graph, score);
            /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
            reevaluateBackward(graph, nodes, arrow, globalScoreHash);
        }

        return score;
    }

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    private void initializeArrowsForward(List <Node> nodes, Graph graph, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        Set <Node> empty = Collections.emptySet();

        for (int j = 0; j < nodes.size(); j++) {

            for (int i = 0; i < nodes.size(); i++) {
                if (j == i) continue;

                Node _x = nodes.get(i);
                Node _y = nodes.get(j);

                if (getKnowledge().edgeForbidden(_x.getName(),
                        _y.getName())) {
                    continue;
                }

                Set <Node> naYX = empty;
                Set <Node> t = empty;

                if (!validSetByKnowledge(_x, _y, t, true)) {
                    continue;
                }
                /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
                double bump = insertEval(_x, _y, t, naYX, graph, globalScoreHash);

                if (bump > minJump) {
                    Arrow arrow = new Arrow(bump, i, j, t, naYX, nodes);
                    lookupArrows[i][j] = new HashSet <Arrow>();
                    sortedArrows.add(arrow);
                    lookupArrows[i][j].add(arrow);
                }
            }
        }


    }

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    private void initializeArrowsBackward(Graph graph, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        List <Node> nodes = graph.getNodes();
        sortedArrowsBackwards = new TreeSet <Arrow>();
        lookupArrowsBackwards = new HashSet[nodes.size()][nodes.size()];

        List <Edge> graphEdges = graph.getEdges();

        for (Edge edge : graphEdges) {
            Node _x = edge.getNode1();
            Node _y = edge.getNode2();

            int i = nodesHash.get(edge.getNode1());
            int j = nodesHash.get(edge.getNode2());

            if (!getKnowledge().noEdgeRequired(_x.getName(),
                    _y.getName())) {
                continue;
            }
            /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
            if (Edges.isDirectedEdge(edge)) {
                calculateArrowsBackward(i, j, nodes, graph, globalScoreHash);
            } else {
                calculateArrowsBackward(i, j, nodes, graph, globalScoreHash);
                calculateArrowsBackward(j, i, nodes, graph, globalScoreHash);
            }

        }
    }

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    private void reevaluateFoward(Graph graph, List <Node> nodes, Arrow arrow, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        Node x = nodes.get(arrow.getX());
        Node y = nodes.get(arrow.getY());

        for (int _w = 0; _w < nodes.size(); _w++) {
            Node w = nodes.get(_w);
            if (w == x) continue;
            if (w == y) continue;

            /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
            if (!graph.isAdjacentTo(w, x)) {
                calculateArrowsForward(_w, arrow.getX(), nodes, graph, globalScoreHash);

                if (graph.isAdjacentTo(w, y)) {
                    calculateArrowsForward(arrow.getX(), _w, nodes, graph, globalScoreHash);
                }
            }
            /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
            if (!graph.isAdjacentTo(w, y)) {
                calculateArrowsForward(_w, arrow.getY(), nodes, graph, globalScoreHash);

                if (graph.isAdjacentTo(w, x)) {
                    calculateArrowsForward(arrow.getY(), _w, nodes, graph, globalScoreHash);
                }
            }
        }
    }

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    private void reevaluateBackward(Graph graph, List <Node> nodes, Arrow arrow, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        Node x = nodes.get(arrow.getX());
        Node y = nodes.get(arrow.getY());

        for (Node w : graph.getAdjacentNodes(x)) {
            int _w = nodesHash.get(w);

            /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
            calculateArrowsBackward(_w, arrow.getX(), nodes, graph, globalScoreHash);
            calculateArrowsBackward(arrow.getX(), _w, nodes, graph, globalScoreHash);
        }

        for (Node w : graph.getAdjacentNodes(y)) {
            int _w = nodesHash.get(w);

            /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
            calculateArrowsBackward(_w, arrow.getX(), nodes, graph, globalScoreHash);
            calculateArrowsBackward(arrow.getX(), _w, nodes, graph, globalScoreHash);
        }
    }

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    private void calculateArrowsForward(int i, int j, List <Node> nodes, Graph graph, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        if (i == j) {
            return;
        }

        Node _x = nodes.get(i);
        Node _y = nodes.get(j);

        if (graph.isAdjacentTo(_x, _y)) {
            return;
        }

        if (getKnowledge().edgeForbidden(_x.getName(),
                _y.getName())) {
            return;
        }

        Set <Node> naYX = findNaYX(_x, _y, graph);

        if (lookupArrows[i][j] != null) {
            for (Arrow arrow : lookupArrows[i][j]) {
                sortedArrows.remove(arrow);
            }

            lookupArrows[i][j] = null;
        }

        List <Node> tNeighbors = getTNeighbors(_x, _y, graph);
        List <Set <Node>> tSubsets = powerSet(tNeighbors);

        for (Set <Node> t : tSubsets) {
            if (!validSetByKnowledge(_x, _y, t, true)) {
                continue;
            }

            double bump = insertEval(_x, _y, t, naYX, graph, globalScoreHash);
            Arrow arrow = new Arrow(bump, i, j, t, naYX, nodes);

//            System.out.println(arrow);

            if (bump > minJump) {
                if (lookupArrows[i][j] == null) {
                    lookupArrows[i][j] = new HashSet <Arrow>();
                }
                sortedArrows.add(arrow);
                lookupArrows[i][j].add(arrow);
            }
        }
    }

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    private void calculateArrowsBackward(int i, int j, List <Node> nodes, Graph graph, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        if (i == j) {
            return;
        }

        Node _x = nodes.get(i);
        Node _y = nodes.get(j);

        if (!graph.isAdjacentTo(_x, _y)) {
            return;
        }

        if (!getKnowledge().noEdgeRequired(_x.getName(),
                _y.getName())) {
            return;
        }

        Set <Node> naYX = findNaYX(_x, _y, graph);


        if (lookupArrowsBackwards[i][j] != null) {
            for (Arrow arrow : lookupArrowsBackwards[i][j]) {
                sortedArrowsBackwards.remove(arrow);
            }

            lookupArrowsBackwards[i][j] = null;
        }

        List <Node> hNeighbors = getHNeighbors(_x, _y, graph);
        List <Set <Node>> hSubsets = powerSet(hNeighbors);

        for (Set <Node> h : hSubsets) {
        	/* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
            double bump = deleteEval(_x, _y, h, naYX, graph, globalScoreHash);
            Arrow arrow = new Arrow(bump, i, j, h, naYX, nodes);

//            System.out.println("Calculate backwards " + arrow);

            if (bump > minNeg) {
                if (lookupArrowsBackwards[i][j] == null) {
                    lookupArrowsBackwards[i][j] = new HashSet <Arrow>();
                }

                sortedArrowsBackwards.add(arrow);
                lookupArrowsBackwards[i][j].add(arrow);
            }
        }
    }

    /**
     * True iff the f cutoff should be used in the forward search.
     */
    public boolean isUseFCutoff() {
        return useFCutoff;
    }


    /**
     * Evaluate the Insert(X, Y, T) operator (Definition 12 from Chickering, 2002).
     */

    public void setUseFCutoff(boolean useFCutoff) {
        this.useFCutoff = useFCutoff;
    }

    /**
     * Evaluate the Delete(X, Y, T) operator (Definition 12 from Chickering, 2002).
     */

    /**
     * The P value for the f cutoff, if used.
     */
    public double getfCutoffP() {
        return fCutoffP;
    }

    /*
    * Do an actual insertion
    * (Definition 12 from Chickering, 2002).
    **/

    public void setfCutoffP(double fCutoffP) {
        if (fCutoffP < 0.0 || fCutoffP > 1.0) {
            throw new IllegalArgumentException();
        }

        this.fCutoffP = fCutoffP;
    }

    /**
     * Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.
     * Gets passed to the scoring function which checks hash before computing the
     * new scores
     */
    private double insertEval(Node x, Node y, Set <Node> t, Set <Node> naYX, Graph graph, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {

        // set1 contains x; set2 does not.
        Set <Node> set2 = new HashSet <Node>(naYX);
        set2.addAll(t);
        set2.addAll(graph.getParents(y));
        Set <Node> set1 = new HashSet <Node>(set2);
        set1.add(x);
        /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
        double score = scoreGraphChange(y, set1, set2, globalScoreHash);

        return score;
    }

    /*
     * Test if the candidate insertion is a valid operation
     * (Theorem 15 from Chickering, 2002).
     **/

    /**
     * the call for localScoreCache replaced. @Diljot,Chris
     * Gets passed to the scoring function to check the hash if we have the scores before computing
     */
    private double deleteEval(Node x, Node y, Set <Node> h, Set <Node> naYX, Graph graph, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {

        // set2 contains x; set1 does not.
        Set <Node> set2 = new HashSet <Node>(naYX);
        set2.removeAll(h);
        set2.addAll(graph.getParents(y));
        set2.add(x);
        Set <Node> set1 = new HashSet <Node>(set2);
        set1.remove(x);
        /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
        return scoreGraphChange(y, set1, set2, globalScoreHash);
    }

    private void insert(Node x, Node y, Set <Node> t, Graph graph, double score, boolean log, double bump) {
        if (graph.isAdjacentTo(x, y)) {
            throw new IllegalArgumentException(x + " and " + y + " are already adjacent in the graph.");
        }

        Edge trueEdge = null;

        if (trueGraph != null) {
            Node _x = trueGraph.getNode(x.getName());
            Node _y = trueGraph.getNode(y.getName());
            trueEdge = trueGraph.getEdge(_x, _y);
        }

        graph.addDirectedEdge(x, y);

        if (log) {
            String label = trueGraph != null && trueEdge != null ? "*" : "";
            TetradLogger.getInstance().log("insertedEdges", graph.getNumEdges() + ". INSERT " + graph.getEdge(x, y) +
                    " " + t +
                    " (" + nf.format(score) + ") " + label);
            System.out.println(graph.getNumEdges() + ". INSERT " + graph.getEdge(x, y) +
                    " " + t +
                    " (" + nf.format(score) + ", " + bump + ") " + label);
        }

        for (Node _t : t) {
            Edge oldEdge = graph.getEdge(_t, y);

            if (oldEdge == null) throw new IllegalArgumentException("Not adjacent: " + _t + ", " + y);

            if (!Edges.isUndirectedEdge(oldEdge)) {
                throw new IllegalArgumentException("Should be undirected: " + oldEdge);
            }

            graph.removeEdge(_t, y);
            graph.addDirectedEdge(_t, y);

            if (log) {
                TetradLogger.getInstance().log("directedEdges", "--- Directing " + oldEdge + " to " +
                        graph.getEdge(_t, y));
                System.out.println("--- Directing " + oldEdge + " to " +
                        graph.getEdge(_t, y));
            }
        }
    }

    //---Background knowledge methods.

    /*
    private void addRequiredEdges(Graph graph) {
        for (Iterator<KnowledgeEdge> it =
                this.getKnowledge().requiredEdgesIterator(); it.hasNext();) {
            KnowledgeEdge next = it.next();
            String a = next.getFrom();
            String b = next.getTo();
            Node nodeA = null, nodeB = null;
            Iterator<Node> itn = graph.getNodes().iterator();
            while (itn.hasNext() && (nodeA == null || nodeB == null)) {
                Node nextNode = itn.next();
                if (nextNode.getName().equals(a)) {
                    nodeA = nextNode;
                }
                if (nextNode.getName().equals(b)) {
                    nodeB = nextNode;
                }
            }
            if (!graph.isAncestorOf(nodeB, nodeA)) {
                graph.removeEdge(nodeA, nodeB);
                graph.addDirectedEdge(nodeA, nodeB);
                TetradLogger.getInstance().log("insertedEdges", "Adding edge by knowledge: " + graph.getEdge(nodeA, nodeB));
            }
        }
        for (Iterator<KnowledgeEdge> it =
                getKnowledge().forbiddenEdgesIterator(); it.hasNext();) {
            KnowledgeEdge next = it.next();
            String a = next.getFrom();
            String b = next.getTo();
            Node nodeA = null, nodeB = null;
            Iterator<Node> itn = graph.getNodes().iterator();
            while (itn.hasNext() && (nodeA == null || nodeB == null)) {
                Node nextNode = itn.next();
                if (nextNode.getName().equals(a)) {
                    nodeA = nextNode;
                }
                if (nextNode.getName().equals(b)) {
                    nodeB = nextNode;
                }
            }
            if (nodeA != null && nodeB != null && graph.isAdjacentTo(nodeA, nodeB) &&
                    !graph.isChildOf(nodeA, nodeB)) {
                if (!graph.isAncestorOf(nodeA, nodeB)) {
                    graph.removeEdges(nodeA, nodeB);
                    graph.addDirectedEdge(nodeB, nodeA);
                    TetradLogger.getInstance().log("insertedEdges", "Adding edge by knowledge: " + graph.getEdge(nodeB, nodeA));
                }
            }
        }
    }
    */

    /**
     * Do an actual deletion (Definition 13 from Chickering, 2002).
     */
    private void delete(Node x, Node y, Set <Node> subset, Graph graph, double score, boolean log, double bump) {

        Edge trueEdge = null;

        if (trueGraph != null) {
            Node _x = trueGraph.getNode(x.getName());
            Node _y = trueGraph.getNode(y.getName());
            trueEdge = trueGraph.getEdge(_x, _y);
        }

        if (log) {
            Edge oldEdge = graph.getEdge(x, y);

            String label = trueGraph != null && trueEdge != null ? "*" : "";
            TetradLogger.getInstance().log("deletedEdges", (graph.getNumEdges() - 1) + ". DELETE " + oldEdge +
                    " " + subset +
                    " (" + nf.format(score) + ") " + label);
            System.out.println((graph.getNumEdges() - 1) + ". DELETE " + oldEdge +
                    " " + subset +
                    " (" + nf.format(score) + ", " + bump + ") " + label);
        }

        graph.removeEdge(x, y);

        for (Node h : subset) {
            graph.removeEdge(y, h);
            graph.addDirectedEdge(y, h);

            if (log) {
                Edge oldEdge = graph.getEdge(y, h);
                TetradLogger.getInstance().log("directedEdges", "--- Directing " + oldEdge + " to " +
                        graph.getEdge(y, h));
            }

            if (Edges.isUndirectedEdge(graph.getEdge(y, h))) {
                if (!graph.isAdjacentTo(x, h)) throw new IllegalArgumentException("Not adjacent: " + x + ", " + h);

                graph.removeEdge(x, h);
                graph.addDirectedEdge(x, h);

                if (log) {
                    Edge oldEdge = graph.getEdge(x, h);
                    TetradLogger.getInstance().log("directedEdges", "--- Directing " + oldEdge + " to " +
                            graph.getEdge(x, h));
                }
            }
        }
    }

    private boolean validInsert(Node x, Node y, Set <Node> t, Set <Node> naYX, Graph graph) {
        Set <Node> union = new HashSet <Node>(t);
        union.addAll(naYX);

        if (!isClique(union, graph)) {
            return false;
        }

        if (existsUnblockedSemiDirectedPath(y, x, union, graph)) {
            return false;
        }

        return true;
    }

    //--Auxiliary methods.

    /**/
    private void addRequiredEdges(Graph graph) {
        for (Iterator <KnowledgeEdge> it =
             this.getKnowledge().requiredEdgesIterator(); it.hasNext(); ) {
            KnowledgeEdge next = it.next();
            String a = next.getFrom();
            String b = next.getTo();
            Node nodeA = null, nodeB = null;
            Iterator <Node> itn = graph.getNodes().iterator();
            while (itn.hasNext() && (nodeA == null || nodeB == null)) {
                Node nextNode = itn.next();
                if (nextNode.getName().equals(a)) {
                    nodeA = nextNode;
                }
                if (nextNode.getName().equals(b)) {
                    nodeB = nextNode;
                }
            }
            if (!graph.isAncestorOf(nodeB, nodeA)) {
                graph.removeEdge(nodeA, nodeB);

                /**************/
                if (!(nodeA == null || nodeB == null)) {/*******************/ /*changed August 27. Need to not add edges with one part null.*/
                    graph.addDirectedEdge(nodeA, nodeB);
                    TetradLogger.getInstance().log("insertedEdges", "Adding edge by knowledge: " + graph.getEdge(nodeA, nodeB));
                }
            }
        }
    }

    /**
     * Use background knowledge to decide if an insert or delete operation does not orient edges in a forbidden
     * direction according to prior knowledge. If some orientation is forbidden in the subset, the whole subset is
     * forbidden.
     */
    private boolean validSetByKnowledge(Node x, Node y, Set <Node> subset,
                                        boolean insertMode) {
        if (insertMode) {
            for (Node node : subset) {
                if (getKnowledge().edgeForbidden(node.getName(),
                        y.getName())) {
                    return false;
                }
            }
        } else {
            for (Node nextElement : subset) {
                if (getKnowledge().edgeForbidden(x.getName(),
                        nextElement.getName())) {
                    return false;
                }
                if (getKnowledge().edgeForbidden(y.getName(),
                        nextElement.getName())) {
                    return false;
                }
            }
        }
        return true;
    }

    public boolean existsUnblockedSemiDirectedPath(Node node1, Node node2, Set <Node> cond, Graph graph) {
        return existsUnblockedSemiDirectedPathVisit(node1, node2,
                new LinkedList <Node>(), graph, cond);
    }

    private boolean existsUnblockedSemiDirectedPathVisit(Node node1, Node nodes2,
                                                         LinkedList <Node> path, Graph graph, Set <Node> cond) {
        if (cond.contains(node1)) return false;
        if (path.size() > 6) return false;
        path.addLast(node1);

        for (Edge edge : graph.getEdges(node1)) {
            Node child = Edges.traverseSemiDirected(node1, edge);

            if (child == null) {
                continue;
            }

            if (nodes2 == child) {
                return true;
            }

            if (path.contains(child)) {
                continue;
            }

            if (existsUnblockedSemiDirectedPathVisit(child, nodes2, path, graph, cond)) {
                return true;
            }
        }

        path.removeLast();
        return false;
    }

    /**
     * Completes a pattern that was modified by an insertion/deletion operator Based on the algorithm described on
     * Appendix C of (Chickering, 2002).
     */
    private void rebuildPattern(Graph graph) {
        SearchGraphUtils.basicPattern(graph);
        addRequiredEdges(graph);
        pdagWithBk(graph, getKnowledge());

        TetradLogger.getInstance().log("rebuiltPatterns", "Rebuilt pattern = " + graph);
    }

    /**
     * Fully direct a graph with background knowledge. I am not sure how to adapt Chickering's suggested algorithm above
     * (dagToPdag) to incorporate background knowledge, so I am also implementing this algorithm based on Meek's 1995
     * UAI paper. Notice it is the same implemented in PcSearch. </p> *IMPORTANT!* *It assumes all colliders are
     * oriented, as well as arrows dictated by time order.*
     */
    private void pdagWithBk(Graph graph, Knowledge knowledge) {
        MeekRules rules = new MeekRules();
        rules.setAggressivelyPreventCycles(this.aggressivelyPreventCycles);
        rules.setKnowledge(knowledge);
        rules.orientImplied(graph);
    }

    private void setDataSet(DataSet dataSet) {
        List <String> _varNames = dataSet.getVariableNames();

        this.varNames = _varNames.toArray(new String[0]);
        this.variables = dataSet.getVariables();
        this.dataSet = dataSet;
        this.discrete = dataSet.isDiscrete();

        if (!isDiscrete()) {
            this.covariances = dataSet.getCovarianceMatrix();
        }

        this.sampleSize = dataSet.getNumRows();
    }

    private void buildIndexing(Graph graph) {
        this.hashIndices = new HashMap <Node, Integer>();
        for (Node next : graph.getNodes()) {
            for (int i = 0; i < this.varNames.length; i++) {
                if (this.varNames[i].equals(next.getName())) {
                    this.hashIndices.put(next, i);
                    break;
                }
            }
        }
    }

    //===========================SCORING METHODS===========================//
    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    public double scoreGraph(Graph graph, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        Graph dag = SearchGraphUtils.dagFromPattern(graph);
        double score = 0.;

        for (Node y : dag.getNodes()) {
            Set <Node> parents = new HashSet <Node>(dag.getParents(y));
            int nextIndex = -1;
            for (int i = 0; i < getVariables().size(); i++) {
                if (this.varNames[i].equals(y.getName())) {
                    nextIndex = i;
                    break;
                }
            }
            int parentIndices[] = new int[parents.size()];
            Iterator <Node> pi = parents.iterator();
            int count = 0;
            while (pi.hasNext()) {
                Node nextParent = pi.next();
                for (int i = 0; i < getVariables().size(); i++) {
                    if (this.varNames[i].equals(nextParent.getName())) {
                        parentIndices[count++] = i;
                        break;
                    }
                }
            }

            if (this.isDiscrete()) {
            	/* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
                score += localDiscreteScore(nextIndex, parentIndices, y, parents, globalScoreHash);
            } else {
                score += localSemScore(nextIndex, parentIndices);
            }

            // ==================Writing to the file=====================
            //
            //This part is not required, just writing all the scores calculated to the file
            //to make the comparison easier (after making changes to code).
            try {
                File file = new File("GlobalScoreHash-Final");

                if (!file.exists()) {
                    file.createNewFile();
                }

                FileWriter fileWriter = new FileWriter(file.getName(), true);
                BufferedWriter bufferWriter = new BufferedWriter(fileWriter);
                bufferWriter.write("The Node:" + y + "\n The Parents: " + parents + "\n The Score:" + score);
                bufferWriter.write("\n_______________________________________________________________________________\n");
                bufferWriter.close();
            } catch (Exception e) {
                System.out.println("Error Writing");
            }

            //=======End Writing to File =======================
            //
        }
        return score;
    }

    /* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
    private double scoreGraphChange(Node y, Set <Node> parents1,
                                    Set <Node> parents2, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {
        int yIndex = hashIndices.get(y);

        Double score1 = null;
        if (globalScoreHash.containsKey(y)) {
            if (globalScoreHash.get(y).containsKey(parents1)) {
                score1 = globalScoreHash.get(y).get(parents1);
            }
        }

        if (score1 == null) {
            int parentIndices1[] = new int[parents1.size()];

            int count = 0;
            for (Node aParents1 : parents1) {
                parentIndices1[count++] = (hashIndices.get(aParents1));
            }

            if (isDiscrete()) {
            	/* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
                score1 = localDiscreteScore(yIndex, parentIndices1, y, parents1, globalScoreHash);
            } else {
                score1 = localSemScore(yIndex, parentIndices1);
            }

            // ==================Writing to the file=====================
            //
            //This part is not required, just writing all the scores calculated to the file
            //to make the comparison easier (after making changes to code).
            try {
                File file = new File("GlobalScoreHash-Final");

                if (!file.exists()) {
                    file.createNewFile();
                }

                FileWriter fileWriter = new FileWriter(file.getName(), true);
                BufferedWriter bufferWriter = new BufferedWriter(fileWriter);
                bufferWriter.write("The Node:" + y + "\n The Parents: " + parents1 + "\n The Score:" + score1);
                bufferWriter.write("\n_______________________________________________________________________________\n");
                bufferWriter.close();
            } catch (Exception e) {
                System.out.println("Error Writing");
            }

            //=======End File =========================

            //We are not going to add the scores to the hash yet. The score will
            //be added later inside the BdeuScore.java file.
            //globalScoreHash.get(y).put(parents1, score1);
        }

        Double score2 = null;
        if (globalScoreHash.containsKey(y)) {
            if (globalScoreHash.get(y).containsKey(parents2)) {
                score2 = globalScoreHash.get(y).get(parents2);
            }
        }

        if (score2 == null) {
            int parentIndices2[] = new int[parents2.size()];

            int count2 = 0;
            for (Node aParents2 : parents2) {
                parentIndices2[count2++] = (hashIndices.get(aParents2));
            }

            if (isDiscrete()) {
            	/* Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.*/
                score2 = localDiscreteScore(yIndex, parentIndices2, y, parents2, globalScoreHash);
            } else {
                score2 = localSemScore(yIndex, parentIndices2);
            }
            //Not adding the scores into the hash. All the score hashing is done in BdeuScore.java
            //globalScoreHash.get(y).put(parents2, score2);

            //===========Writing File =======================//
            //This part writes the scores and the concerned parents and the children to the file
            //makes it easy to compare the results.
            try {
                File file = new File("GlobalScoreHash-Final");

                if (!file.exists()) {
                    file.createNewFile();
                }

                FileWriter fileWriter = new FileWriter(file.getName(), true);
                BufferedWriter bufferWriter = new BufferedWriter(fileWriter);
                bufferWriter.write("The Node:" + y + "\n The Parents: " + parents2 + "\n The Score:" + score2);
                bufferWriter.write("\n_______________________________________________________________________________\n");
                bufferWriter.close();
            } catch (Exception e) {
                System.out.println("Error Writing");
            }

            //=======End File =========================
        }

        // That is, the score for the variable set that contains x minus the score
        // for the variable set that does not contain x.
        return score1 - score2;
    }

    /**
     * Diljot,Chris : using the globalScoreHash from BayesBase.java in the function.
     * The function is in BDeuScore.java and it uses the globalScoreHash to hash the scores.The hashing
     * done in the BdeuScore.java file.
     */
    private double localDiscreteScore(int i, int parents[], Node y, Set <Node> parentNodes, Map <Node, Map <Set <Node>, Double>> globalScoreHash) {

        return getDiscreteScore().localScore(i, parents, y, parentNodes, globalScoreHash);

//        double oldScore = localScoreCache.get(i, parents);
//
//        if (!Double.isNaN(oldScore)) {
//            return oldScore;
//        }
//        // Number of categories for i.
//        int r = numCategories(i);
//
//        // Numbers of categories of parents.
//        int dims[] = new int[parents.length];
//
//        for (int p = 0; p < parents.length; p++) {
//            dims[p] = numCategories(parents[p]);
//        }
//
//        // Number of parent states.
//        int q = 1;
//        for (int p = 0; p < parents.length; p++) {
//            q *= dims[p];
//        }
//
//        // Conditional cell counts of data for i given parents(i).
//        int n_ijk[][] = new int[q][r];
//        int n_ij[] = new int[q];
//
//        int values[] = new int[parents.length];
//
//        for (int n = 0; n < sampleSize(); n++) {
//            for (int p = 0; p < parents.length; p++) {
//                int parentValue = dataSet().getInt(n, parents[p]);
//
//                if (parentValue == -99) {
//                    throw new IllegalStateException("Please remove or impute " +
//                            "missing values.");
//                }
//
//                values[p] = parentValue;
//            }
//
//            int childValue = dataSet().getInt(n, i);
//
//            if (childValue == -99) {
//                throw new IllegalStateException("Please remove or impute missing " +
//                        "values (record " + n + " column " + i + ")");
//
//            }
//
//            n_ijk[getRowIndex(dims, values)][childValue]++;
//        }
//
//        // Row sums.
//        for (int j = 0; j < q; j++) {
//            for (int k = 0; k < r; k++) {
//                n_ij[j] += n_ijk[j][k];
//            }
//        }
//
//        //Finally, compute the score
//        double score = (r - 1) * q * Math.log(getStructurePrior());
//
//        for (int j = 0; j < q; j++) {
//            for (int k = 0; k < r; k++) {
//                score += ProbUtils.lngamma(
//                        getSamplePrior() / (r * q) + n_ijk[j][k]);
//            }
//
//            score -= ProbUtils.lngamma(getSamplePrior() / q + n_ij[j]);
//        }
//
//        score += q * ProbUtils.lngamma(getSamplePrior() / q);
////        score -= (r * q) * ProbUtils.lngamma(getSamplePrior() / (r * q));
//        score -= r * ProbUtils.lngamma(getSamplePrior() / (r * q));
//
//        localScoreCache.add(i, parents, score);
//
//        return score;
    }

    private int numCategories(int i) {
        return ((DiscreteVariable) dataSet().getVariable(i)).getNumCategories();
    }

    /**
     * Calculates the sample likelihood and BIC score for i given its parents in a simple SEM model.
     */
    private double localSemScore(int i, int[] parents) {

        // Calculate the unexplained variance of i given z1,...,zn
        // considered as a naive Bayes model.
        double variance = getCovMatrix().get(i, i);
        int n = sampleSize();
        double k = parents.length + 1;

//        if (regression == null) {
//            regression = new RegressionDataset(dataSet());
//        }
//
//        List<Node> variables = dataSet.getVariables();
//        Node target = variables.get(i);
//
//        List<Node> regressors = new ArrayList<Node>();
//
//        for (int parent : parents) {
//            regressors.add(variables.get(parent));
//        }
//
//        RegressionResult result = regression.regress(target, regressors);
//
//        double[] residuals = result.getResiduals().toArray();
//
//        double _variance = StatUtils.variance(residuals);

        if (parents.length > 0) {

            // Regress z onto i, yielding regression coefficients b.
            DoubleMatrix2D Czz = getCovMatrix().viewSelection(parents, parents);
            DoubleMatrix2D inverse = invert(Czz, parents);
            DoubleMatrix1D Cyz = getCovMatrix().viewColumn(i);
            Cyz = Cyz.viewSelection(parents);
            DoubleMatrix1D b = algebra().mult(inverse, Cyz);

//            System.out.println("B = " + MatrixUtils.toString(b.toArray()));

            variance -= algebra().mult(Cyz, b);
        }

        if (variance == 0) {
            StringBuilder b = localModelString(i, parents);
            this.logger.log("info", b.toString());
            this.logger.log("info", "Zero residual variance; returning negative infinity.");
            return Double.NEGATIVE_INFINITY;
        }

        double penalty = getPenaltyDiscount();

        // This is the full -BIC formula.
//        return -0.5 n * Math.log(variance) - n * Math.log(2. * Math.PI) - n
//                - penalty * k * Math.log(n);
//        return -.5 * n * (Math.log(variance) + Math.log(2 * Math.PI) + 1) - penalty * k * Math.log(n);

        // 2L - k ln n = 2 * BIC
//        return -n * (Math.log(variance) + Math.log(2 * Math.PI) + 1) - penalty * k * Math.log(n);

        // This is the formula with contant terms for fixed n removed.
        return -n * Math.log(variance) - penalty * k * Math.log(n);
    }

    /**
     * Compute the local BDeu score of (i, parents(i)). See (Chickering, 2002).
     */

    private StringBuilder localModelString(int i, int[] parents) {
        StringBuilder b = new StringBuilder();
        b.append(("*** "));
        b.append(variables.get(i));

        if (parents.length == 0) {
            b.append(" with no parents");
        } else {
            b.append(" with parents ");

            for (int j = 0; j < parents.length; j++) {
                b.append(variables.get(parents[j]));

                if (j < parents.length - 1) {
                    b.append(",");
                }
            }
        }
        return b;
    }


//    private double localDiscreteBicScore(int i, int[] parents) {
//
//        // Number of categories for i.
//        int r = numCategories(i);
//
//        // Numbers of categories of parents.
//        int dims[] = new int[parents.length];
//
//        for (int p = 0; p < parents.length; p++) {
//            dims[p] = numCategories(parents[p]);
//        }
//
//        // Number of parent states.
//        int q = 1;
//        for (int p = 0; p < parents.length; p++) {
//            q *= dims[p];
//        }
//
//        // Conditional cell counts of data for i given parents(i).
//        double cell[][] = new double[q][r];
//
//        int values[] = new int[parents.length];
//
//        for (int n = 0; n < sampleSize(); n++) {
//            for (int p = 0; p < parents.length; p++) {
//                int value = dataSet().getInt(n, parents[p]);
//
//                if (value == -99) {
//                    throw new IllegalStateException("Complete data expected.");
//                }
//
//                values[p] = value;
//            }
//
//            int value = dataSet().getInt(n, i);
//
//            if (value == -99) {
//                throw new IllegalStateException("Complete data expected.");
//
//            }
//
//            cell[getRowIndex(dims, values)][value]++;
//        }
//
//        // Calculate row sums.
//        double rowSum[] = new double[q];
//
//        for (int j = 0; j < q; j++) {
//            for (int k = 0; k < r; k++) {
//                rowSum[j] += cell[j][k];
//            }
//        }
//
//        // Calculate log prob data given structure.
//        double score = 0.0;
//
//        for (int j = 0; j < q; j++) {
//            if (rowSum[j] == 0) {
//                continue;
//            }
//
//            for (int k = 0; k < r; k++) {
//                double count = cell[j][k];
//                double prob = count / rowSum[j];
//                score += count * Math.log(prob);
//            }
//        }
//
//        // Subtract penalty.
//        double numParams = q * (r - 1);
//        return score - numParams / 2. * Math.log(sampleSize());
//    }

    private DoubleMatrix2D invert(DoubleMatrix2D czz, int[] parents) {
        DoubleMatrix2D inverse;
        try {
//            inverse = algebra().inverse(czz);
//                inverse = MatrixUtils.inverse(czz);
            inverse = MatrixUtils.ginverse(czz);
        } catch (Exception e) {
            StringBuilder buf = new StringBuilder();
            buf.append("Could not invert matrix for variables: ");

            for (int j = 0; j < parents.length; j++) {
                buf.append(variables.get(parents[j]));

                if (j < parents.length - 1) {
                    buf.append(", ");
                }
            }

            throw new IllegalArgumentException(buf.toString());
        }
        return inverse;
    }

    private int sampleSize() {
        return this.sampleSize;
    }

    private List <Node> getVariables() {
        return variables;
    }

    private DoubleMatrix2D getCovMatrix() {
        return covariances;
    }

    private void setCovMatrix(ICovarianceMatrix covarianceMatrix) {
        this.covariances = covarianceMatrix.getMatrix();
        List <String> _varNames = covarianceMatrix.getVariableNames();

        this.varNames = _varNames.toArray(new String[0]);
        this.variables = covarianceMatrix.getVariables();
        this.sampleSize = covarianceMatrix.getSampleSize();
    }

    private Algebra algebra() {
        return algebra;
    }

    private DataSet dataSet() {
        return dataSet;
    }

    private double getStructurePrior() {
        return structurePrior;
    }

    public void setStructurePrior(double structurePrior) {
        if (getDiscreteScore() != null) {
            getDiscreteScore().setStructurePrior(structurePrior);
        }
        this.structurePrior = structurePrior;
    }

    private double getSamplePrior() {
        return samplePrior;
    }

    public void setSamplePrior(double samplePrior) {
        if (getDiscreteScore() != null) {
            getDiscreteScore().setSamplePrior(samplePrior);
        }
        this.samplePrior = samplePrior;
    }

    private boolean isDiscrete() {
        return discrete;
    }

    private void fireGraphChange(Graph graph) {
        for (PropertyChangeListener l : getListeners()) {
            l.propertyChange(new PropertyChangeEvent(this, "graph", null, graph));
        }
    }

    private List <PropertyChangeListener> getListeners() {
        if (listeners == null) {
            listeners = new ArrayList <PropertyChangeListener>();
        }
        return listeners;
    }

    private void storeGraph(Graph graph, double score) {
        if (!isStoreGraphs()) return;

        if (topGraphs.isEmpty() || score > topGraphs.first().getScore()) {
            Graph graphCopy = new EdgeListGraph(graph);

            System.out.println("Storing " + score + " " + graphCopy);

            topGraphs.add(new ScoredGraph(graphCopy, score));

            if (topGraphs.size() > getNumPatternsToStore()) {
                topGraphs.remove(topGraphs.first());
            }
        }
    }

    public LocalDiscreteScore getDiscreteScore() {
        return discreteScore;
    }

    public void setDiscreteScore(LocalDiscreteScore discreteScore) {
        if (discreteScore.getDataSet() != dataSet) {
            throw new IllegalArgumentException("Must use the same data set.");
        }
        this.discreteScore = discreteScore;
    }

    private static class Arrow implements Comparable {
        private double bump;
        private int x;
        private int y;
        private Set <Node> hOrT;
        private Set <Node> naYX;
        private List <Node> nodes;

        public Arrow(double bump, int x, int y, Set <Node> hOrT, Set <Node> naYX, List <Node> nodes) {
            this.bump = bump;
            this.x = x;
            this.y = y;
            this.hOrT = hOrT;
            this.naYX = naYX;
            this.nodes = nodes;
        }

        public double getBump() {
            return bump;
        }

        public int getX() {
            return x;
        }

        public int getY() {
            return y;
        }

        public Set <Node> getHOrT() {
            return hOrT;
        }

        public Set <Node> getNaYX() {
            return naYX;
        }

        // Sorting is by bump, high to low.

        public int compareTo(Object o) {
            Arrow info = (Arrow) o;
            return new Double(info.getBump()).compareTo(new Double(getBump()));
        }

        public String toString() {
            return "Arrow<" + nodes.get(x) + "->" + nodes.get(y) + " bump = " + bump + " t = " + hOrT + " naYX = " + naYX + ">";
        }
    }
}




