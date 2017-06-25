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

package edu.cmu.tetrad.test;

import edu.cmu.tetrad.data.*;
import edu.cmu.tetrad.graph.Graph;
import edu.cmu.tetrad.graph.GraphUtils;
import edu.cmu.tetrad.graph.Node;
import edu.cmu.tetrad.sem.SemIm;
import edu.cmu.tetrad.sem.SemPm;
import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;


/**
 * Tests the column discretizer.
 *
 * @author Joseph Ramsey jdramsey@andrew.cmu.edu
 */
public final class TestDiscretizer extends TestCase {

    /**
     * Standard constructor for JUnit test cases.
     */
    public TestDiscretizer(final String name) {
        super(name);
    }


    public static void testBreakpointCalculation() {
        double[] data = {13, 1.2, 2.2, 4.5, 12.005, 5.5, 10.1, 7.5, 3.4};
        double[] breakpoints = Discretizer.getEqualFrequencyBreakPoints(data, 3);

        assertTrue(breakpoints.length == 2);
        assertEquals(4.5, breakpoints[0]);
        assertEquals(10.1, breakpoints[1]);

        Discretizer.Discretization dis = Discretizer.discretize(data, breakpoints, "after", Arrays.asList("0", "1", "2"));
        System.out.println(dis);

        breakpoints = Discretizer.getEqualFrequencyBreakPoints(data, 4);
        assertTrue(breakpoints.length == 3);

        assertEquals(3.4, breakpoints[0]);
        assertEquals(5.5, breakpoints[1]);
        assertEquals(10.1, breakpoints[2]);

    }

    public static void testManualDiscretize() {
        Node x = new ContinuousVariable("X");
        List <Node> nodes = Collections.singletonList(x);
        DataSet data = new ColtDataSet(9, nodes);

        data.setDouble(0, 0, 13.0);
        data.setDouble(1, 0, 1.2);
        data.setDouble(2, 0, 2.2);
        data.setDouble(3, 0, 4.5);
        data.setDouble(4, 0, 12.005);
        data.setDouble(5, 0, 5.5);
        data.setDouble(6, 0, 10.1);
        data.setDouble(7, 0, 7.5);
        data.setDouble(8, 0, 3.4);

        System.out.println(data);

        Discretizer discretizer = new Discretizer(data);
        discretizer.setVariablesCopied(true);

        discretizer.equalCounts(x, 3);
        DataSet discretized = discretizer.discretize();

        System.out.println(discretized);

        assertEquals(discretized.getInt(0, 0), 2);
        assertEquals(discretized.getInt(1, 0), 0);
        assertEquals(discretized.getInt(2, 0), 0);
        assertEquals(discretized.getInt(3, 0), 1);
        assertEquals(discretized.getInt(4, 0), 2);
        assertEquals(discretized.getInt(5, 0), 1);
        assertEquals(discretized.getInt(6, 0), 2);
        assertEquals(discretized.getInt(7, 0), 1);
        assertEquals(discretized.getInt(8, 0), 0);

    }

    /**
     * This method uses reflection to collect up all of the test methods from
     * this class and return them to the test runner.
     */
    public static Test suite() {

        // Edit the name of the class in the parens to match the name
        // of this class.
        return new TestSuite(TestDiscretizer.class);
    }

    // Causes a package cycle.
    public void testManualDiscretize2() {
        Graph graph = GraphUtils.randomDag(5, 0, 5, 3, 3, 3, false);
        SemPm pm = new SemPm(graph);
        SemIm im = new SemIm(pm);
        DataSet data = im.simulateData(100, false);

        List <Node> nodes = data.getVariables();

        Discretizer discretizer = new Discretizer(data);
        discretizer.setVariablesCopied(true);

        discretizer.equalCounts(nodes.get(0), 3);
        discretizer.equalIntervals(nodes.get(1), 2);
        discretizer.equalCounts(nodes.get(2), 5);
        discretizer.equalIntervals(nodes.get(3), 8);
        discretizer.equalCounts(nodes.get(4), 4);

        DataSet discretized = discretizer.discretize();

        System.out.println(discretized);

        assertEquals(maxInColumn(discretized, 0), 2);
        assertEquals(maxInColumn(discretized, 1), 1);
        assertEquals(maxInColumn(discretized, 2), 4);
        assertEquals(maxInColumn(discretized, 3), 7);
        assertEquals(maxInColumn(discretized, 4), 3);
    }

    public void testManualDiscretize3() {
        Graph graph = GraphUtils.randomDag(5, 0, 5, 3, 3, 3, false);
        SemPm pm = new SemPm(graph);
        SemIm im = new SemIm(pm);
        DataSet data = im.simulateData(100, false);

        List <Node> nodes = data.getVariables();

        Discretizer discretizer = new Discretizer(data);
        discretizer.setVariablesCopied(true);

        discretizer.setVariablesCopied(true);
        discretizer.equalCounts(nodes.get(0), 3);

        DataSet discretized = discretizer.discretize();

        System.out.println(discretized);

        assertTrue(discretized.getVariable(0) instanceof DiscreteVariable);
        assertTrue(discretized.getVariable(1) instanceof ContinuousVariable);
        assertTrue(discretized.getVariable(2) instanceof ContinuousVariable);
        assertTrue(discretized.getVariable(3) instanceof ContinuousVariable);
        assertTrue(discretized.getVariable(4) instanceof ContinuousVariable);
    }

    /*
     * @param dataSet A discrete data set.
     * @param column the column in question.
     * @return the max value in that column.
     */
    private int maxInColumn(DataSet dataSet, int column) {
        int max = -1;

        for (int i = 0; i < dataSet.getNumRows(); i++) {
            int value = dataSet.getInt(i, column);
            if (value > max) max = value;
        }

        return max;
    }

//    public static void testDiscrete() {
//        final int[] data = {1, 2, 1, 2, 0, 5, 3, 2, 3, 4, 3, 5};
//
//        DiscreteVariable variable = new DiscreteVariable("before", 6);
//
//        int[] remap = new int[]{0, 0, 1, 1, 2, 2};
//        List<String> categories =
//                Arrays.asList(new String[]{"lo", "med", "hi"});
//
//        Discretization discretization = Discretization.discretize(variable, data, remap, "after", categories);
//
//        System.out.println(discretization);
//
//        List<String> discretizedCategories =
//                discretization.getVariable().getCategories();
//        int[] discretizedData = discretization.getSimulatedData();
//
//        assertEquals("lo", discretizedCategories.get(discretizedData[0]));
//        assertEquals("med", discretizedCategories.get(discretizedData[1]));
//        assertEquals("lo", discretizedCategories.get(discretizedData[2]));
//        assertEquals("med", discretizedCategories.get(discretizedData[3]));
//        assertEquals("lo", discretizedCategories.get(discretizedData[4]));
//        assertEquals("hi", discretizedCategories.get(discretizedData[5]));
//    }

    public void testContinuous() {
        final double[] data = {1, 2, 2.5, 3, 4, 5};

        double[] cutoffs = new double[]{2.5, 3.2};
        List <String> categories = Arrays.asList("lo", "med", "hi");

        Discretizer.Discretization discretization = Discretizer.discretize(data, cutoffs, "after", categories);

        System.out.println(discretization);

        List <String> discretizedCategories =
                discretization.getVariable().getCategories();
        int[] discretizedData = discretization.getData();

        assertEquals("lo", discretizedCategories.get(discretizedData[0]));
        assertEquals("lo", discretizedCategories.get(discretizedData[1]));
        assertEquals("med", discretizedCategories.get(discretizedData[2]));
        assertEquals("med", discretizedCategories.get(discretizedData[3]));
        assertEquals("hi", discretizedCategories.get(discretizedData[4]));
        assertEquals("hi", discretizedCategories.get(discretizedData[5]));
    }
}
