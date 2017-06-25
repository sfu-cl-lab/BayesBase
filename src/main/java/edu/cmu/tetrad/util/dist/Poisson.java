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

package edu.cmu.tetrad.util.dist;

import edu.cmu.tetrad.util.RandomUtil;

/**
 * Created by IntelliJ IDEA. User: jdramsey Date: Jan 15, 2008 Time: 5:06:49 PM
 * To change this template use File | Settings | File Templates.
 */

/**
 * Wraps a chi square distribution for purposes of drawing random samples.
 * Methods are provided to allow parameters to be manipulated in an interface.
 *
 * @author Joseph Ramsey
 */
public class Poisson implements Distribution {
    static final long serialVersionUID = 23L;

    private double mean;

    public Poisson(double mean) {
        this.mean = mean;
    }

    /**
     * Generates a simple exemplar of this class to test serialization.
     *
     * @return The exemplar.
     * @see edu.cmu.TestSerialization
     * @see edu.cmu.tetradapp.util.TetradSerializableUtils
     */
    @SuppressWarnings({"UnusedDeclaration"})
    public static Poisson serializableInstance() {
        return new Poisson(1);
    }

    @Override
    public int getNumParameters() {
        return 1;
    }

    @Override
    public String getName() {
        return "Distibution";
    }

    @Override
    public void setParameter(int index, double value) {
        if (index == 0) {
            mean = value;
        }

        throw new IllegalArgumentException();
    }

    @Override
    public double getParameter(int index) {
        if (index == 0) {
            return mean;
        }

        throw new IllegalArgumentException();
    }

    @Override
    public String getParameterName(int index) {
        if (index == 0) {
            return "Mean";
        }

        throw new IllegalArgumentException();
    }

    @Override
    public double nextRandom() {
        return RandomUtil.getInstance().nextPoisson(mean);
    }

    @Override
    public String toString() {
        return "Poisson(" + mean + ")";
    }
}

