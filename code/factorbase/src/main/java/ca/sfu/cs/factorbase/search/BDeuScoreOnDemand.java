package ca.sfu.cs.factorbase.search;

import java.math.BigDecimal;
import java.util.Arrays;
import java.util.List;
import java.util.Set;

import ca.sfu.cs.factorbase.data.ContingencyTable;
import ca.sfu.cs.factorbase.data.DataSetMetaData;
import ca.sfu.cs.factorbase.data.FunctorNodesInfo;
import ca.sfu.cs.factorbase.data.RandomVariableAssignment;
import ca.sfu.cs.factorbase.database.FactorBaseDataBase;
import ca.sfu.cs.factorbase.exception.DataBaseException;
import ca.sfu.cs.factorbase.exception.ScoringException;
import edu.cmu.tetrad.util.ProbUtils;

/**
 * Class to compute the BDeuScore for a given child and its parents.
 */
public class BDeuScoreOnDemand implements DiscreteLocalScore {

    private FactorBaseDataBase database;
    private FunctorNodesInfo functorInfos;
    private double samplePrior;
    private double structurePrior;


    /**
     * Create a new BDeuScore object for the given database and functor nodes, using the given hyperparameters.
     *
     * @param database - FactorBaseDataBase to get the count information from.
     * @param functorInfos - the functor nodes of interest in the given {@code FactorBaseDataBase}.
     * @param samplePrior - the equivalent sample size (N').
     * @param structurePrior - the prior probability for the network structure.
     */
    public BDeuScoreOnDemand (
        FactorBaseDataBase database,
        FunctorNodesInfo functorNodeInfos,
        double samplePrior,
        double structurePrior
    ) {
        this.database = database;
        this.functorInfos = functorNodeInfos;
        this.samplePrior = samplePrior;
        this.structurePrior = structurePrior;
    }


    @Override
    public double localScore(String child, Set<String> parents) throws ScoringException {
        // Number of child states.
        int r = this.functorInfos.getNumberOfStates(child);

        // Number of parent states.
        int q = 1;
        for (String parent : parents) {
            q *= this.functorInfos.getNumberOfStates(parent);
        }

        try {
            ContingencyTable ct = this.database.getContingencyTable(this.functorInfos, child, parents, r * q);
            DataSetMetaData meta = ct.getMetaData();

            // Calculate score.
            BigDecimal score = new BigDecimal((r - 1) * q * Math.log(this.structurePrior));

            for (List<RandomVariableAssignment> parentAssignments : meta.getStates(ct.getParentColumnIndices())) {
                double countsSum = 0;
                long counts;
                for (int childStateIndex = 0; childStateIndex < r; childStateIndex++) {
                    RandomVariableAssignment childAssignment = new RandomVariableAssignment(ct.getChildColumnIndex(), childStateIndex);
                    counts = ct.getCounts(childAssignment, parentAssignments);
                    countsSum += counts;
                    score = score.add(new BigDecimal(ProbUtils.lngamma(this.samplePrior / (r * q) + counts)));
                }

                score = score.subtract(new BigDecimal(ProbUtils.lngamma(this.samplePrior / q + countsSum)));
            }

            score = score.add(new BigDecimal(q * ProbUtils.lngamma(this.samplePrior / q)));
            score = score.subtract(new BigDecimal((r * q) * ProbUtils.lngamma(this.samplePrior / (r * q))));

            return score.doubleValue();
        } catch (DataBaseException e) {
            throw new ScoringException(
                "An error occurred when attempting to compute the score for " + child +
                " with parents " + Arrays.toString(parents.toArray()),
                e
            );
        }
    }
}