package ca.sfu.cs.factorbase.learning;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.sql.Connection;

/*zqian, April 1st, 2014 fixed the bug of too many connections by adding con4.close()*/


/*Jun 25,2013 @zqian
 * 
 * Trying to conquer the bottleneck of creating false tables (the join issue) by implementing our sort_merge algorithm.
 * Great stuff!
 * 
 * Here we have some different versions.
 * for version 3, naive implementing of sort merge with "load into" command in terms of efficiency issue of mysql insertion.
 * for version 4, concatenating the order by columns into one column when version 3 can not finish the order by .
 * 
 * for version 5, it's a kind of more complicated approach by pre-compressing all the attribute columns into one column, and then employing concatenating trick again on order by part.
 *   this version still has some bugs that need to be investagiated.
 *   
 * Preconditions: database_BN  has been created with lattice information and functor information.
 *  
 * */

import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.StringJoiner;
import java.util.logging.Logger;

import ca.sfu.cs.common.Configuration.Config;
import ca.sfu.cs.factorbase.data.DataSet;
import ca.sfu.cs.factorbase.data.DataSetMetaData;
import ca.sfu.cs.factorbase.data.FunctorNodesInfo;
import ca.sfu.cs.factorbase.data.MySQLDataExtractor;
import ca.sfu.cs.factorbase.database.FactorBaseDataBaseInfo;
import ca.sfu.cs.factorbase.database.MySQLFactorBaseDataBase;
import ca.sfu.cs.factorbase.exception.DataExtractionException;
import ca.sfu.cs.factorbase.lattice.LatticeGenerator;
import ca.sfu.cs.factorbase.lattice.RelationshipLattice;
import ca.sfu.cs.factorbase.util.MySQLScriptRunner;
import ca.sfu.cs.factorbase.util.QueryGenerator;
import ca.sfu.cs.factorbase.util.RuntimeLogger;
import ca.sfu.cs.factorbase.util.Sort_merge3;

public class CountsManager {

    private static Connection dbConnection;
    private static final String AND_SEPARATOR = " AND ";
    private static final String CSV_SEPARATOR = ", ";
    private static final String COUNTS_SUBQUERY_PLACEHOLDER = "@@C_SUBQUERY@@";
    private static final String FALSE_SUBQUERY_PLACEHOLDER = "@@F_SUBQUERY@@";
    private static int tableID;
    private static Map<String, String> ctTablesCache = new HashMap<String, String>();
    private static Set<String> relationTables;
    private static FactorBaseDataBaseInfo dbInfo;
    private static String databaseName_std;
    private static String dbUsername;
    private static String dbPassword;
    private static String dbaddress;
    private static boolean generatePDPInfo;
    private static String linkCorrelation;
    private static long dbTemporaryTableSize;
    /*
     * cont is Continuous
     * ToDo: Refactor
     */
    private static String cont;
    private static Logger logger = Logger.getLogger(CountsManager.class.getName());

    static {
        setVarsFromConfig();
    }


    /**
     * Build the CT tables based on the FunctorSet.
     *
     * @param countingStrategy - {@link CountingStrategy} to indicate how counts related tables should be generated.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    public static void buildCT(
        CountingStrategy countingStrategy
    ) throws SQLException {
        RuntimeLogger.addLogEntry(dbConnection);
        try (Statement statement = dbConnection.createStatement()) {
            statement.execute("DROP SCHEMA IF EXISTS " + dbInfo.getCTDatabaseName() + ";");
            statement.execute("CREATE SCHEMA " + dbInfo.getCTDatabaseName() + " /*M!100316 COLLATE utf8_general_ci*/;");
        }

        // Propagate metadata based on the FunctorSet.
        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        RelationshipLattice relationshipLattice = propagateFunctorSetInfo(dbConnection);

        // building CT tables for Rchain
        CTGenerator(relationshipLattice, countingStrategy);
    }


    /**
     * Use the FunctorSet to generate the necessary metadata for constructing CT tables.
     *
     * @param dbConnection - connection to the "_BN" database.
     * @return the relationship lattice created based on the FunctorSet.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static RelationshipLattice propagateFunctorSetInfo(Connection dbConnection) throws SQLException {
        // Transfer metadata from the "_setup" database to the "_BN" database based on the FunctorSet.
        long start = System.currentTimeMillis();
        MySQLScriptRunner.callSP(
            dbConnection,
            "cascadeFS"
        );
        RuntimeLogger.updateLogEntry(dbConnection, "cascadeFS", System.currentTimeMillis() - start);

        // Generate the relationship lattice based on the FunctorSet.
        start = System.currentTimeMillis();
        RelationshipLattice relationshipLattice = LatticeGenerator.generate(
            dbConnection,
            databaseName_std
        );
        RuntimeLogger.updateLogEntry(dbConnection, "lattice", System.currentTimeMillis() - start);

        // TODO: Add support for Continuous = 1.
        if (cont.equals("1")) {
            throw new UnsupportedOperationException("Not Implemented Yet!");
        } else {
            start = System.currentTimeMillis();
            MySQLScriptRunner.callSP(
                dbConnection,
                "populateMQ"
            );
            RuntimeLogger.updateLogEntry(dbConnection, "populateMQ", System.currentTimeMillis() - start);
        }

        start = System.currentTimeMillis();
        MySQLScriptRunner.callSP(
            dbConnection,
            "populateMQRChain"
        );
        RuntimeLogger.updateLogEntry(dbConnection, "populateMQRChain", System.currentTimeMillis() - start);

        return relationshipLattice;
    }


    /**
     * Generate the contingency tables for the given relationship lattice.
     *
     * @param relationshipLattice - the relationship lattice used to determine which contingency tables to generate.
     * @param countingStrategy - {@link CountingStrategy} to indicate how counts related tables should be generated.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static void CTGenerator(
        RelationshipLattice relationshipLattice,
        CountingStrategy countingStrategy
    ) throws SQLException {
        int latticeHeight = relationshipLattice.getHeight();

        /**
         *  If we are building the RChain "_counts" tables for the Ondemand or Hybrid method, start from a height of 2.
         *  Since we cache the CT tables for RNodes, we might not need to construct the "_counts" for RNodes as they
         *  are a prerequisite for constructing CT tables.  Also, for the Hybrid method, a subquery is used instead of
         *  materializing the "_counts" table for RNodes.
         */
        int startingHeight = 1;
        if (!countingStrategy.isPrecount()) {
            startingHeight = 2;
        }

        // Build the counts tables for the RChains.
        buildRChainCounts(
            dbInfo.getCTDatabaseName(),
            relationshipLattice,
            countingStrategy.useProjection(),
            countingStrategy.getStorageEngine(),
            startingHeight
        );

        long l = System.currentTimeMillis(); //@zqian : CT table generating time
           // handling Pvars, generating pvars_counts       
        buildPVarsCounts(countingStrategy);
        long end = System.currentTimeMillis();
        RuntimeLogger.updateLogEntry(dbConnection, "buildPVarsCounts", end - l);
        RuntimeLogger.logRunTimeDetails(logger, "buildPVarsCounts", l, end);

        // preparing the _join part for _CT tables
        long start = System.currentTimeMillis();
        Map<String, String> joinTableQueries = createJoinTableQueries();
        RuntimeLogger.updateLogEntry(dbConnection, "createJoinTableQueries", System.currentTimeMillis() - start);

        if (linkCorrelation.equals("1") && relationshipLattice.getHeight() != 0) {
            start = System.currentTimeMillis();

            // Retrieve the first level of the lattice.
            List<FunctorNodesInfo> rchainInfos = relationshipLattice.getRChainsInfo(1);

            BuildRNodesCTMethod<
                String,
                String,
                CountingStrategy,
                String,
                String,
                String,
                SQLException
            > buildCTMethod = CountsManager::buildRNodesCT;

            // Use the buildRNodesCTFromCache method if we have been specified to read the counts from the cache.
            if (countingStrategy.useCTCache()) {
                buildCTMethod = CountsManager::buildRNodesCTFromCache;
            }

            // Build the CT tables for the first level of the relationship lattice.
            long ctAllStart = System.currentTimeMillis();
            String finalTableName = null;
            for (FunctorNodesInfo rnodeInfo : rchainInfos) {
                String rnode = rnodeInfo.getID();
                String shortRNode = rnodeInfo.getShortID();
                String ctTableName = shortRNode + "_CT";
                String ctCreationQuery = buildRNodeCTCreationQuery(rnode, shortRNode, joinTableQueries);

                buildCTMethod.apply(
                    dbInfo.getCTDatabaseName(),
                    ctTableName,
                    countingStrategy,
                    ctCreationQuery,
                    rnode,
                    shortRNode
                );

                finalTableName = ctTableName;
            }
            RuntimeLogger.logRunTimeDetails(logger, "buildRChainsCT-length=1", ctAllStart, System.currentTimeMillis());

            //building the _CT tables. Going up the Rchain lattice
            for(int len = 2; len <= latticeHeight; len++) {
                ctAllStart = System.currentTimeMillis();
                rchainInfos = relationshipLattice.getRChainsInfo(len);
                finalTableName = buildRChainsCT(rchainInfos, len, joinTableQueries, countingStrategy.getStorageEngine());
                RuntimeLogger.logRunTimeDetails(logger, "buildRChainsCT-length=" + len, ctAllStart, System.currentTimeMillis());
            }

            if (generatePDPInfo) {
                logPDPOutput(
                    dbInfo.getCTDatabaseName(),
                    finalTableName,
                    false,
                    latticeHeight,
                    start,
                    System.currentTimeMillis()
                );
            }

            RuntimeLogger.updateLogEntry(dbConnection, "buildFlatStarCT", System.currentTimeMillis() - start);
        }

        long l2 = System.currentTimeMillis();  //@zqian
        logger.fine("Building Time(ms) for ALL CT tables:  "+(l2-l)+" ms.\n");
    }


    /**
     * Build the CT table for the given RNode (relationship lattice length = 1).
     *
     * @param targetDatabaseName - the name of the database to generate the table in.
     * @param ctTableName - the name of the  table to generate.
     * @param countingStrategy - {@link CountingStrategy} to indicate how counts related tables should be generated.
     * @param ctCreationQuery - SELECT query used to create the CT table.
     * @param rnode - the name of the RNode to generate the CT table for.
     * @param shortRNode - the short name of the RNode to generate the CT table for.
     * @return True if the CT table was generated from a cache; this method doesn't use a cache, so it always returns
     *         false.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static boolean buildRNodesCT(
        String targetDatabaseName,
        String ctTableName,
        CountingStrategy countingStrategy,
        String ctCreationQuery,
        String rnode,
        String shortRNode
    ) throws SQLException {
        long start = System.currentTimeMillis();
        String countsTableSubQuery = generateCountsTableQuery(
            dbInfo.getCTDatabaseName(),
            rnode,
            shortRNode,
            countingStrategy.useProjection()
        );

        // If we are doing using the Precount or Ondemand method, we read from a materialized table to avoid executing
        // expensive joins twice.
        if (countingStrategy.isOndemand()) {
            long countsStart = System.currentTimeMillis();
            String tableName;
            if (generatePDPInfo) {
                String[] subQueryComponents = generateCountsTableQueryDetails(
                    dbInfo.getCTDatabaseName(),
                    rnode,
                    shortRNode,
                    countingStrategy.useProjection()
                );

                tableName = generateCountsTableAndPDPInfo(
                    dbInfo.getCTDatabaseName(),
                    shortRNode,
                    countingStrategy.getStorageEngine(),
                    subQueryComponents
                );
            } else {
                tableName = generateCountsTable(
                    dbInfo.getCTDatabaseName(),
                    shortRNode,
                    countingStrategy.getStorageEngine(),
                    countsTableSubQuery
                );
            }
            RuntimeLogger.logRunTimeDetails(logger, "buildRChainCounts-length=1", countsStart, System.currentTimeMillis());

            countsTableSubQuery = "SELECT * FROM " + dbInfo.getCTDatabaseName() + "." + tableName;
        } else if (countingStrategy.isPrecount()) {
            countsTableSubQuery = "SELECT * FROM " + dbInfo.getCTDatabaseName() + "." + shortRNode + "_counts";
        }

        // Add runtime to a column used to add to the "Counts" portion and subtract from the "Moebius Join" portion.
        RuntimeLogger.updateLogEntry(dbConnection, "buildRNodeCounts", System.currentTimeMillis() - start);

        // Build the _star table subquery.
        String starTableSubQuery = buildRNodeStarQuery(rnode, shortRNode);

        // Build the _flat table.
        buildRNodeFlat(rnode, shortRNode, countingStrategy.getStorageEngine(), countsTableSubQuery);

        // Build the _false table subquery.
        String falseTableSubQuery = buildRNodeFalseQuery(starTableSubQuery, shortRNode);
        ctCreationQuery = ctCreationQuery.replaceFirst(COUNTS_SUBQUERY_PLACEHOLDER, countsTableSubQuery);
        ctCreationQuery = ctCreationQuery.replaceFirst(FALSE_SUBQUERY_PLACEHOLDER, falseTableSubQuery);

        // Build the _CT table.
        String createCTQuery = QueryGenerator.createSimpleCreateTableQuery(
            ctTableName,
            countingStrategy.getStorageEngine(),
            ctCreationQuery
        );

        dbConnection.setCatalog(targetDatabaseName);
        RuntimeLogger.logExecutedQuery(logger, createCTQuery);
        try (Statement statement = dbConnection.createStatement()) {
            statement.executeUpdate(createCTQuery);
        }

        // This method is not supposed to use a cache, so it should always return false.
        return false;
    }


    /**
     * Build the CT table for the given RNode (relationship lattice length = 1) using the CT cache database.
     *
     * @param targetDatabaseName - the name of the database to generate the table in.
     * @param ctTableName - the name of the  table to generate.
     * @param countingStrategy - {@link CountingStrategy} to indicate how counts related tables should be generated.
     * @param ctCreationQuery - SELECT query used to create the CT table.
     * @param rnode - the name of the RNode to generate the CT table for.
     * @param shortRNode - the short name of the RNode to generate the CT table for.
     * @return True if the CT table was generated from a cache; otherwise false.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static boolean buildRNodesCTFromCache(
        String targetDatabaseName,
        String ctTableName,
        CountingStrategy countingStrategy,
        String ctCreationQuery,
        String rnode,
        String shortRNode
    ) throws SQLException {
        String ctTablesCacheKey = ctTableName + ctCreationQuery;
        String cacheTableName = ctTablesCache.get(ctTablesCacheKey);
        boolean cacheUsed = cacheTableName != null;
        if (cacheTableName == null) {
            // Create the table in the CT cache database.
            cacheTableName = ctTableName + "_" + tableID;
            tableID++;
            buildRNodesCT(
                dbInfo.getCTCacheDatabaseName(),
                cacheTableName,
                countingStrategy,
                ctCreationQuery,
                rnode,
                shortRNode
            );

            ctTablesCache.put(ctTablesCacheKey, cacheTableName);
        }

        dbConnection.setCatalog(dbInfo.getCTDatabaseName());
        try (Statement createViewStatement = dbConnection.createStatement()) {
            String viewQuery =
                "CREATE VIEW " + ctTableName + " AS " +
                "SELECT * " +
                "FROM " + dbInfo.getCTCacheDatabaseName() + "." + cacheTableName;
            createViewStatement.executeUpdate(viewQuery);
        }

        return cacheUsed;
    }


    /**
     * Generate the global counts tables.
     */
    public static void buildRChainsGlobalCounts() throws SQLException {
        RuntimeLogger.addLogEntry(dbConnection);

        // Propagate metadata based on the FunctorSet.
        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        RelationshipLattice relationshipLattice = propagateFunctorSetInfo(dbConnection);

        // Generate the global counts in the "_global_counts" database.
        buildRChainCounts(
            dbInfo.getGlobalCountsDatabaseName(),
            relationshipLattice,
            false,
            "MEMORY",
            1
        );
    }


    /**
     * Build the "_counts" tables for the RChains in the given relationship lattice.
     *
     * @param dbTargetName - name of the database to create the "_counts" tables in.
     * @param relationshipLattice - the relationship lattice containing the RChains to build the "_counts" tables for.
     * @param buildByProjection - True if the counts table should be built by projecting the necessary information from
                                  the global counts table; otherwise false.
     * @param storageEngine - the storage engine to use for the tables created when executing this method.
     * @param startingHeight - the height of the RChain to start building the counts tables for.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static void buildRChainCounts(
        String dbTargetName,
        RelationshipLattice relationshipLattice,
        boolean buildByProjection,
        String storageEngine,
        int startingHeight
    ) throws SQLException {
        long start = System.currentTimeMillis();
        int latticeHeight = relationshipLattice.getHeight();

        // Building the <RChain>_counts tables.
        boolean copyToCT = true;
        if(linkCorrelation.equals("1")) {
            copyToCT = false;
        }

        // Generate the counts tables and copy their values to the CT tables if specified to.
        long countsStart;
        for(int len = startingHeight; len <= latticeHeight; len++) {
            countsStart = System.currentTimeMillis();
            generateCountsTables(
                dbTargetName,
                relationshipLattice.getRChainsInfo(len),
                copyToCT,
                buildByProjection,
                storageEngine
            );
            RuntimeLogger.logRunTimeDetails(logger, "buildRChainCounts-length=" + len, countsStart, System.currentTimeMillis());
        }

        RuntimeLogger.updateLogEntry(dbConnection, "buildRChainCounts", System.currentTimeMillis() - start);
    }


    /**
     * setVarsFromConfig
     * ToDo : Remove Duplicate definitions across java files
     */
    private static void setVarsFromConfig() {
        Config conf = new Config();
        dbInfo = new FactorBaseDataBaseInfo(conf);
        databaseName_std = conf.getProperty("dbname");
        dbUsername = conf.getProperty("dbusername");
        dbPassword = conf.getProperty("dbpassword");
        dbaddress = conf.getProperty("dbaddress");
        dbTemporaryTableSize = Math.round(1024 * 1024 * 1024 * Double.valueOf(conf.getProperty("dbtemporarytablesize")));
        linkCorrelation = conf.getProperty("LinkCorrelations");
        cont = conf.getProperty("Continuous");
        String loggingLevel = conf.getProperty("LoggingLevel");
        generatePDPInfo = loggingLevel.equals("runtimeDetails") || loggingLevel.equals("debug");
    }


    /**
     * Log the necessary information to generate a partial dependency plot (PDP) for constructing "_CT" tables.
     *
     * @param database - the name of the database containing the "_CT" table to get the PDP information for.
     * @param table - the name of the table to get the PDP information for.
     * @param cacheUsed - True if a cache was used to generate the "_CT" table; otherwise false.
     * @param rchainLength - the RChain length that the given "_CT" table was generated for.
     * @param start - table creation start time of the given "_CT" table.
     * @param end - table creation end time of the given "_CT" table.
     */
    private static void logPDPOutput(
        String database,
        String table,
        boolean cacheUsed,
        int rchainLength,
        long start,
        long end
    ) {
        try {
            MySQLDataExtractor extractor = new MySQLDataExtractor(
                dbConnection.prepareStatement(
                    "SELECT * " +
                    "FROM " + database + ".`" + table + "` " +
                    "WHERE " + dbInfo.getCountColumnName() + " > 0;"
                ),
                dbInfo.getCountColumnName(),
                dbInfo.isDiscrete()
            );
            DataSet data = extractor.extractData();
            DataSetMetaData metadata = data.getMetaData();
            int countColumnIndex = metadata.getCountColumnIndex();

            // L is the length of the RChain the CT table was built for.
            int L = rchainLength;

            // C is the number of non-ID columns, excluding the "MULT" column.
            int C = metadata.getVariableNames().size();
            BigInteger totalNumberOfValuesPerColumn = new BigInteger("0");
            for (int i = 0; i <= C; i++) {
                if (i != countColumnIndex) {
                    String numberOfValues = String.valueOf(metadata.getNumberOfStates(i));
                    totalNumberOfValuesPerColumn = totalNumberOfValuesPerColumn.add(new BigInteger(numberOfValues));
                }
            }

            // V is the average number of possible values each non-ID column contains.
            // Note: The division below will take the floor of the result.
            String V = String.valueOf(totalNumberOfValuesPerColumn.divide(new BigInteger(String.valueOf(C))));

            String cacheUsedAsString = String.valueOf(cacheUsed).substring(0, 1).toUpperCase();
            RuntimeLogger.pdpOutput(
                logger,
                "CT Build Time",
                "cached" + cacheUsedAsString + ",L" + L + ",C" + C + ",V" + V,
                start,
                end
            );
        } catch (DataExtractionException | SQLException e) {
            logger.warning("Ran into a problem collecting the PDP data - " + e.getCause());
        }
    }


    /**
     * Connect to database via MySQL JDBC driver
     */
    private static Connection connectDB(String databaseName) throws SQLException {
        Properties connectionProperties = MySQLFactorBaseDataBase.getConnectionStringProperties(
            dbUsername,
            dbPassword
        );

        String CONN_STR = "jdbc:" + dbaddress + "/" + databaseName;
        try {
            java.lang.Class.forName("com.mysql.cj.jdbc.Driver");
        } catch (Exception ex) {
            logger.severe("Unable to load MySQL JDBC driver");
        }
        return DriverManager.getConnection(CONN_STR, connectionProperties);
    }


    /**
     * Building the _CT tables. Going up the relationship lattice (When RChain.length >=2).
     * <p>
     * For each RChain of the specified length:<br>
     * 1. Find the list of members for the RChain.  Suppose first member is rnid1.<br>
     * 2. Initialize current_ct = rchain_counts after summing out the relational attributes of rnid1.<br>
     * 3. Current list = all members of RChain minus rnid1.  Find CT table for current list =
     *    Select rows where all members of current list are true.  Add 1nodes of rnid1.<br>
     * 4. Compute false table using the results of 2 and 3 (basically 2 - 3).<br>
     * 5. Union false table with current_ct to get new ct where all members of current list are true.<br>
     * 6. Repeat with current list as initial list until list is empty.<br><br>
     * Example:<br>
     * 1. RChain = R3,R2,R1.  rnid1 = R3.<br>
     * 2. Find `R3,R2,R1_counts`.  Sum out fields from R3 to get `R2,R1-R3_flat1`.<br>
     * 3. Current list = R2,R1.  Find `R2,R1_ct` where R1 = T, R2 = T.  Add 1nodes of R3 (multiplying) to get
     *    `R2,R1-R3_star`.<br>
     * 4. Compute `R2,R1-R3_false` = `R2,R1-R3_star - `R2,R1-R3_flat1`.<br>
     * 5. Compute `R2,R1-R3_ct` = `R2,R1-R3_false` Cartesian Product `R3_join` union `R3,R2,R1_counts`.<br>
     * 6. Current list = R1.  Current rnid1 = R2.  Current ct_table = `R2,R1-R3_ct`.
     * </p>
     * @param rchainInfos - FunctorNodesInfos for the RChains to build the "_CT" tables for.
     * @param len - length of the RChains to consider.
     * @param joinTableQueries - {@code Map} to retrieve the associated query to create a derived JOIN table.
     * @param storageEngine - the storage engine to use for the tables created when executing this method.
     * @return the name of the final CT table that gets created.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static String buildRChainsCT(
        List<FunctorNodesInfo> rchainInfos,
        int len,
        Map<String, String> joinTableQueries,
        String storageEngine
    ) throws SQLException {
        int fc=0;
        String finalTableName = null;
        for (FunctorNodesInfo rchainInfo : rchainInfos)
        {
            // Get the short and full form rnids for further use.
            String rchain = rchainInfo.getID();
            String shortRchain = rchainInfo.getShortID();
            // Oct 16 2013
            // initialize the cur_CT_Table, at very beginning we will use _counts table to create the _flat table
            String cur_CT_Table = shortRchain + "_counts";
            // counts represents the ct tables where all relationships in Rchain are true

            //  create new statement
            dbConnection.setCatalog(dbInfo.getBNDatabaseName());
            Statement st1 = dbConnection.createStatement();
            ResultSet rs1 = st1.executeQuery(
                "SELECT removed, short_rnid " +
                "FROM lattice_rel " +
                "JOIN lattice_mapping " +
                "ON lattice_rel.removed = lattice_mapping.orig_rnid " +
                "WHERE child = '" + rchain + "' " +
                "ORDER BY removed ASC;"
            ); // members of rchain

            while(rs1.next())
            {       
                String removed = rs1.getString("removed");
                String removedShort = rs1.getString("short_rnid");
                String BaseName = shortRchain + "_" + removedShort;

                dbConnection.setCatalog(dbInfo.getBNDatabaseName());
                Statement st2 = dbConnection.createStatement();

                //  create select query string  
                ResultSet rs2 = st2.executeQuery(
                    QueryGenerator.createMetaQueriesExtractionQuery(
                        rchain,
                        "Star",
                        "SELECT",
                        removed,
                        false
                    )
                );
                List<String> columns = extractEntries(rs2, "Entries");
                String selectString = String.join(", ", columns);
                rs2.close();
                //  create mult query string
                ResultSet rs3 = st2.executeQuery(
                    QueryGenerator.createMetaQueriesExtractionQuery(
                        rchain,
                        "Star",
                        "FROM",
                        removed,
                        false
                    )
                );
                columns = extractEntries(rs3, "Entries");
                String MultString = makeStarSepQuery(columns);
                rs3.close();
                //  create from query string
                String fromString = String.join(", ", columns);
                //  create where query string
                ResultSet rs5 = st2.executeQuery(
                    QueryGenerator.createMetaQueriesExtractionQuery(
                        rchain,
                        "Star",
                        "WHERE",
                        removed,
                        false
                    )
                );
                columns = extractEntries(rs5, "Entries");
                String whereString = String.join(" AND ", columns);
                rs5.close();
                //  create the final query
                String queryString ="";
                if (!selectString.isEmpty() && !whereString.isEmpty()) {
                    queryString = "Select " +  MultString+ " as `MULT` ,"+selectString + " from " + fromString  + " where " + whereString;
                } else if (!selectString.isEmpty()) {
                    queryString = "Select " +  MultString+ " as `MULT` ,"+selectString + " from " + fromString;
                } else if (!whereString.isEmpty()) {
                    queryString =
                        "SELECT " + MultString + " AS `MULT` " +
                        "FROM " + fromString  + " " +
                        "WHERE " + whereString;
                } else {
                    queryString =
                        "SELECT " + MultString + " AS `MULT` " +
                        "FROM " + fromString;
                }

                dbConnection.setCatalog(dbInfo.getCTDatabaseName());
                Statement st3 = dbConnection.createStatement();

                //make the rnid shorter 
                String rnid_or=removedShort;

                //staring to create the _flat table
                // Oct 16 2013
                // cur_CT_Table should be the one generated in the previous iteration
                // for the very first iteration, it's _counts table

                String cur_flat_Table = removedShort + len + "_" + fc + "_flat";
                String queryStringflat = "SELECT SUM(`" + cur_CT_Table + "`.MULT) AS 'MULT' ";

                if (!selectString.isEmpty()) {
                    queryStringflat +=
                        ", " + selectString + " " +
                        "FROM `" + cur_CT_Table + "` " +
                        "GROUP BY " + selectString + ";";
                } else {
                    queryStringflat +=
                        "FROM `" + cur_CT_Table + "`;";
                }

                String createStringflat = QueryGenerator.createSimpleCreateTableQuery(
                    cur_flat_Table,
                    storageEngine,
                    queryStringflat
                );
                RuntimeLogger.logExecutedQuery(logger, createStringflat);
                st3.execute(createStringflat);      //create flat table

                // Add covering index.
                addCoveringIndex(
                    dbConnection,
                    dbInfo.getCTDatabaseName(),
                    cur_flat_Table
                );

                /**********starting to create _flase table***using sort_merge*******************************/

                // Computing the false table as the MULT difference between the matching rows of the star and flat tables.
                // This is a big join!
                String falseTableSubQuery = Sort_merge3.sort_merge(
                    dbConnection,
                    dbInfo.getCTDatabaseName(),
                    queryString,
                    cur_flat_Table
                );

                // staring to create the CT table
                ResultSet rs_45 = st2.executeQuery(
                    "SELECT column_name AS Entries " +
                    "FROM information_schema.columns " +
                    "WHERE table_schema = '" + dbInfo.getCTDatabaseName() + "' " +
                    "AND table_name = '" + cur_CT_Table + "';"
                );
                columns = extractEntries(rs_45, "Entries");
                String CTJoinString = makeEscapedCommaSepQuery(columns);

                //join false table with join table to add in rnid (= F) and 2nid (= n/a). then can union with CT table
                String QueryStringCT =
                    "SELECT " + CTJoinString + " " +
                    "FROM `" + cur_CT_Table + "` " +
                    "WHERE MULT > 0 " +

                    "UNION ALL " +

                    "SELECT " + CTJoinString + " " +
                    "FROM " +
                        "(" + falseTableSubQuery + ") AS FALSE_TABLE, " +
                        "(" + joinTableQueries.get(rnid_or) + ") AS JOIN_TABLE " +
                    "WHERE MULT > 0;";

                String Next_CT_Table = "";

                if (rs1.next()) {
                    Next_CT_Table = BaseName + "_CT";
                } else {
                    Next_CT_Table = shortRchain + "_CT";
                }

                // Oct 16 2013
                // preparing the CT table for next iteration
                cur_CT_Table = Next_CT_Table;
                finalTableName = cur_CT_Table;

                // Create CT table.
                st3.execute(
                    QueryGenerator.createSimpleCreateTableQuery(
                        Next_CT_Table,
                        storageEngine,
                        QueryStringCT
                    )
                );

                rs1.previous();

                fc++;   

                //  close statements
                st2.close();            
                st3.close();
            }
            st1.close();
            rs1.close();
        }

        return finalTableName;
    }


    /**
     * Build the "_counts" tables for the population variables.
     *
     * @param countingStrategy - {@link CountingStrategy} to indicate how counts related tables should be generated.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static void buildPVarsCounts(CountingStrategy countingStrategy) throws SQLException {
        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        Statement st = dbConnection.createStatement();
        ResultSet rs = st.executeQuery(
            "SELECT " +
                "pvid " +
            "FROM " +
                "PVariables;"
        );

        GeneratePVarsCountsMethod<
            String,
            String,
            List<String>,
            String,
            String,
            SQLException
        > generateCountsMethod = CountsManager::generatePVarsCountsTable;

        // Use the generatePVarsCountsTableFromCache method if we have been specified to read the counts from the cache.
        if (countingStrategy.useCTCache()) {
            generateCountsMethod = CountsManager::generatePVarsCountsTableFromCache;
        }

        while(rs.next()){
            String pvid = rs.getString("pvid");
            String countsTableName = pvid + "_counts";
            String selectQuery = QueryGenerator.createMetaQueriesExtractionQuery(
                pvid,
                "Counts",
                "SELECT",
                null,
                false
            );

            // Extract column aliases.
            List<String> columnAliases;
            dbConnection.setCatalog(dbInfo.getBNDatabaseName());
            try (
                Statement selectStatement = dbConnection.createStatement();
                ResultSet selectResultSet = selectStatement.executeQuery(selectQuery)
            ) {
                columnAliases = extractEntries(selectResultSet, "Entries");
            }

            generateCountsMethod.apply(
                dbInfo.getCTDatabaseName(),
                countsTableName,
                columnAliases,
                countingStrategy.getStorageEngine(),
                pvid
            );
        }

        rs.close();
        st.close();
    }


    /**
     * Generate the "_counts" table for the given population variable.
     *
     * @param targetDatabaseName - the name of the database to generate the "_counts" table in.
     * @param countsTableName - the name of the "_counts" table to generate.
     * @param columnAliases - the alias statements used for the SELECT clause for the "_counts" table to generate.
     * @param storageEngine - the storage engine to use for the "_counts" table to generate.
     * @param pvid - the ID of the population variable that the "_counts" table is for.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static void generatePVarsCountsTable(
        String targetDatabaseName,
        String countsTableName,
        List<String> columnAliases,
        String storageEngine,
        String pvid
    ) throws SQLException {
        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        Statement st = dbConnection.createStatement();
        String selectString = String.join(", ", columnAliases);

        // Create FROM query.
        String fromQuery = QueryGenerator.createMetaQueriesExtractionQuery(
            pvid,
            "Counts",
            "FROM",
            null,
            false
        );

        String fromString;
        try(ResultSet rs = st.executeQuery(fromQuery)) {
            List<String> tables = extractEntries(rs, "Entries");
            fromString = String.join(", ", tables);
        }

        // Create GROUP BY query.
        String groupbyQuery = QueryGenerator.createMetaQueriesExtractionQuery(
            pvid,
            "Counts",
            "GROUPBY",
            null,
            false
        );

        String groupbyString;
        try(ResultSet rs = st.executeQuery(groupbyQuery)) {
            List<String> columns = extractEntries(rs, "Entries");
            groupbyString = String.join(", ", columns);
        }

        // Create WHERE query (groundings) if applicable.
        String whereQuery = QueryGenerator.createMetaQueriesExtractionQuery(
            pvid,
            "Counts",
            "WHERE",
            null,
            false
        );

        String whereString = "";
        try (ResultSet rsGrounding = st.executeQuery(whereQuery)) {
            List<String> predicates = extractEntries(rsGrounding, "Entries");
            if (!predicates.isEmpty()) {
                whereString = " WHERE " + String.join(" AND ", predicates);
            }
        }

        st.close();

        // Create the final query.
        String queryString =
            "SELECT " + selectString + " " +
            "FROM " + fromString +
            whereString;

// This seems unnecessarily complicated even to deal with continuous variables. OS August 22, 2017

        if (!cont.equals("1") && !groupbyString.isEmpty()) {
            queryString = queryString + " GROUP BY " + groupbyString;
        }

        queryString += " HAVING MULT > 0";

        String createString = QueryGenerator.createSimpleCreateTableQuery(
            countsTableName,
            storageEngine,
            queryString
        );

        RuntimeLogger.logExecutedQuery(logger, createString);
        dbConnection.setCatalog(targetDatabaseName);
        try (Statement st2 = dbConnection.createStatement()) {
            st2.execute(createString);
        }
    }


    /**
     * Generate the "_counts" table for the given population variable using the CT cache database.
     * <p>
     * Note: If the "_counts" table can't be found in the CT cache database it will be generated there.
     * </p>
     *
     * @param targetDatabaseName - the name of the database to generate the "_counts" table in.
     * @param countsTableName - the name of the "_counts" table to generate.
     * @param columnAliases - the alias statements used for the SELECT clause for the "_counts" table to generate.
     * @param storageEngine - the storage engine to use for the "_counts" table to generate.
     * @param pvid - the ID of the population variable that the "_counts" table is for.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static void generatePVarsCountsTableFromCache(
        String targetDatabaseName,
        String countsTableName,
        List<String> columnAliases,
        String storageEngine,
        String pvid
    ) throws SQLException {
        StringJoiner csvJoiner = new StringJoiner(",");
        csvJoiner.add(countsTableName);
        String columnNames = makeDelimitedString(columnAliases, ",", " AS ");
        csvJoiner.add(String.join(",", columnNames));

        String ctTablesCacheKey = csvJoiner.toString();

        String cacheTableName = ctTablesCache.get(ctTablesCacheKey);
        if (cacheTableName == null) {
            // Create the table in the CT cache database.
            cacheTableName = countsTableName + "_" + tableID;
            tableID++;
            generatePVarsCountsTable(
                dbInfo.getCTCacheDatabaseName(),
                cacheTableName,
                columnAliases,
                storageEngine,
                pvid
            );

            ctTablesCache.put(ctTablesCacheKey, cacheTableName);
        }

        dbConnection.setCatalog(targetDatabaseName);
        try (Statement createViewStatement = dbConnection.createStatement()) {
            String viewQuery =
                "CREATE VIEW " + countsTableName + " AS " +
                "SELECT * " +
                "FROM " + dbInfo.getCTCacheDatabaseName() + "." + cacheTableName;
            createViewStatement.executeUpdate(viewQuery);
        }
    }


    /**
     * Create the "_counts" tables for the given RChains and copy the counts to the associated CT table if specified
     * to.
     *
     * @param dbTargetName - name of the database to create the "_counts" tables in.
     * @param rchainInfos - FunctorNodesInfos for the RChains to build the "_counts" tables for.
     * @param copyToCT - True if the values in the generated "_counts" table should be copied to the associated "_CT"
     *                   table; otherwise false.
     * @param buildByProjection - True if the counts table should be built by projecting the necessary information from
                                  the global counts table; otherwise false.
     * @param storageEngine - the storage engine to use for the tables created when executing this method.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static void generateCountsTables(
        String dbTargetName,
        List<FunctorNodesInfo> rchainInfos,
        boolean copyToCT,
        boolean buildByProjection,
        String storageEngine
    ) throws SQLException {
        for (FunctorNodesInfo rchainInfo : rchainInfos) {
            // Get the short and full form rnids for further use.
            String rchain = rchainInfo.getID();
            String shortRchain = rchainInfo.getShortID();
            String countsTableSubQuery;

            if (generatePDPInfo && !buildByProjection) {
                String[] subQueryComponents = generateCountsTableQueryDetails(
                    dbTargetName,
                    rchain,
                    shortRchain,
                    buildByProjection
                );

                countsTableSubQuery = subQueryComponents[0];

                generateCountsTableAndPDPInfo(
                    dbTargetName,
                    shortRchain,
                    storageEngine,
                    subQueryComponents
                );
            } else {
                countsTableSubQuery = generateCountsTableQuery(
                    dbTargetName,
                    rchain,
                    shortRchain,
                    buildByProjection
                );

                generateCountsTable(
                    dbTargetName,
                    shortRchain,
                    storageEngine,
                    countsTableSubQuery
                );
            }

            if (copyToCT) {
                dbConnection.setCatalog(dbTargetName);
                String createString_CT =
                    "CREATE TABLE `" + shortRchain + "_CT`" + " AS " +
                        countsTableSubQuery;
                RuntimeLogger.logExecutedQuery(logger, createString_CT);
                try (Statement statement = dbConnection.createStatement()) {
                    statement.execute(createString_CT);
                }
            }
        }
    }


    /**
     * Generate the query for creating the "_counts" table for the given RChain.
     *
     * @param dbTargetName - name of the database to create the "_counts" table in.
     * @param rchain - the full form name of the RChain.
     * @param shortRchain - the short form name of the RChain.
     * @param buildByProjection - True if the counts table should be built by projecting the necessary information from
                                  the global counts table; otherwise false.
     * @param storageEngine - the storage engine to use for the tables created when executing this method.
     * @return the query for creating the "_counts" table.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static String generateCountsTableQuery(
        String dbTargetName,
        String rchain,
        String shortRchain,
        boolean buildByProjection
    ) throws SQLException {
        // Name of the counts table to generate.
        String countsTableName = shortRchain + "_counts";

        // Create new statements.
        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        Statement st2 = dbConnection.createStatement();

        // Create SELECT query string.
        String selectString = createCountsTableSelectString(
            st2,
            rchain,
            buildByProjection
        );

        // Create FROM query string.
        String fromString = createCountsTableFromString(
            st2,
            rchain,
            buildByProjection,
            countsTableName
        );

        // Create WHERE query string.
        String whereString = createCountsTableWhereString(
            st2,
            rchain,
            buildByProjection
        );

        // Create the final query.
        String queryString = createCountsTableFinalQuery(
            st2,
            rchain,
            selectString,
            fromString,
            whereString
        );

        // Close statements.
        st2.close();

        return queryString;
    }


    /**
     * Generate the query for creating the "_counts" table for the given RChain.
     *
     * @param dbTargetName - name of the database to create the "_counts" table in.
     * @param rchain - the full form name of the RChain.
     * @param shortRchain - the short form name of the RChain.
     * @param buildByProjection - True if the counts table should be built by projecting the necessary information from
                                  the global counts table; otherwise false.
     * @return the query for creating the "_counts" table (String[0]), the table references of the FROM clause
     *         (String[1]), and the conditions for the WHERE clause (String[2]).
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static String[] generateCountsTableQueryDetails(
        String dbTargetName,
        String rchain,
        String shortRchain,
        boolean buildByProjection
    ) throws SQLException {
        String[] countsTableQueryDetails = new String[3];

        // Name of the counts table to generate.
        String countsTableName = shortRchain + "_counts";

        // Create new statements.
        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        Statement statement = dbConnection.createStatement();

        // Create SELECT query string.
        String selectString = createCountsTableSelectString(
            statement,
            rchain,
            buildByProjection
        );

        // Create FROM query string.
        String fromString = createCountsTableFromString(
            statement,
            rchain,
            buildByProjection,
            countsTableName
        );

        // Create WHERE query string.
        String whereString = createCountsTableWhereString(
            statement,
            rchain,
            buildByProjection
        );

        // Create the final query.
        String queryString = createCountsTableFinalQuery(
            statement,
            rchain,
            selectString,
            fromString,
            whereString
        );

        // Close statements.
        statement.close();

        countsTableQueryDetails[0] = queryString;
        countsTableQueryDetails[1] = fromString;
        countsTableQueryDetails[2] = whereString;

        return countsTableQueryDetails;
    }


    /**
     * Create the {@code String} for the SELECT clause of the query for creating the "_counts" table for the given
     * RChain.
     *
     * @param statement - {@code Statement} object created by a {@code Connection} to the "_BN" database.
     * @param rchain - the full form name of the RChain.
     * @param buildByProjection - True if the counts table should be built by projecting the necessary information from
                                  the global counts table; otherwise false.
     * @return the column expressions used in the SELECT clause of the query for creating the "_counts" table.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static String createCountsTableSelectString(
        Statement statement,
        String rchain,
        boolean buildByProjection
    ) throws SQLException {
        String selectQuery =
            "SELECT Entries " +
            "FROM MetaQueries " +
            "WHERE Lattice_Point = '" + rchain + "' " +
            "AND ClauseType = 'SELECT' ";

        // If we're trying to project from a "_counts" table we want to SUM(MULT) instead of COUNT(*) so ignore the
        // 'aggregate" EntryType when generating the SELECT string.
        if (buildByProjection) {
            selectQuery += "AND EntryType <> 'aggregate' ";
        }

        selectQuery += "AND TableType = 'Counts';";

        ResultSet rs2 = statement.executeQuery(selectQuery);

        List<String> selectAliases = extractEntries(rs2, "Entries");
        String selectString;
        if (buildByProjection) {
            selectString = makeDelimitedString(selectAliases, ", ", " AS ");
            selectString = "SUM(MULT) AS MULT, " + selectString;
        } else {
            selectString = String.join(", ", selectAliases);
        }

        return selectString;
    }


    /**
     * Create the {@code String} for the FROM clause of the query for creating the "_counts" table for the given
     * RChain.
     *
     * @param statement - {@code Statement} object created by a {@code Connection} to the "_BN" database.
     * @param rchain - the full form name of the RChain.
     * @param buildByProjection - True if the counts table should be built by projecting the necessary information from
                                  the global counts table; otherwise false.
     * @param countsTableName - name of the counts table expected to be found in the "_global_counts" database if we
     *                          are projecting the count information from the "_global_counts" database.
     * @return the table(s) to get the count information from.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static String createCountsTableFromString(
        Statement statement,
        String rchain,
        boolean buildByProjection,
        String countsTableName
    ) throws SQLException {
        String fromString = dbInfo.getGlobalCountsDatabaseName() + ".`" + countsTableName + "`";

        // If we aren't projecting from the global counts table, we need to retrieve the tables that need to be joined
        // in order to generate the counts table.
        if (!buildByProjection) {
            ResultSet rs3 = statement.executeQuery(
                QueryGenerator.createMetaQueriesExtractionQuery(
                    rchain,
                    "Counts",
                    "FROM",
                    null,
                    false
                )
            );

            List<String> fromAliases = extractEntries(rs3, "Entries");
            fromString = String.join(CSV_SEPARATOR, fromAliases);
        }

        return fromString;
    }


    /**
     * Create the {@code String} for the WHERE clause of the query for creating the "_counts" table for the given
     * RChain.
     *
     * @param statement - {@code Statement} object created by a {@code Connection} to the "_BN" database.
     * @param rchain - the full form name of the RChain.
     * @param buildByProjection - True if the counts table should be built by projecting the necessary information from
                                  the global counts table; otherwise false.
     * @return the conditions that are needed to JOIN tables or {@code null} if we are projecting from the global
     *         counts tables.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static String createCountsTableWhereString(
        Statement statement,
        String rchain,
        boolean buildByProjection
    ) throws SQLException {
        String whereString = null;

        // The WHERE clause is for joining tables to generate the counts from and isn't necessary if we are projecting
        // from the global counts table.
        if (!buildByProjection) {
            ResultSet rs4 = statement.executeQuery(
                QueryGenerator.createMetaQueriesExtractionQuery(
                    rchain,
                    "Counts",
                    "WHERE",
                    null,
                    false
                )
            );

            List<String> columns = extractEntries(rs4, "Entries");
            whereString = String.join(AND_SEPARATOR, columns);
        }

        return whereString;
    }


    /**
     * Create the {@code String} of the query for creating the "_counts" table for the given RChain.
     *
     * @param statement - {@code Statement} object created by a {@code Connection} to the "_BN" database.
     * @param rchain - the full form name of the RChain.
     * @param selectString - the {@code String} returned by the
     *                       {@link CountsManager#createCountsTableSelectString(Statement, String, boolean)} method.
     * @param fromString - the {@code String} returned by the {@link CountsManager#createCountsTableFromString(Statement, String, boolean, String)} method.
     * @param whereString - the {@code String} returned by the {@link CountsManager#createCountsTableWhereString(Statement, String, boolean)} method.
     * @return the query for creating the "_counts" table for the given RChain.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static String createCountsTableFinalQuery(
        Statement statement,
        String rchain,
        String selectString,
        String fromString,
        String whereString
    ) throws SQLException {
        String queryString =
            "SELECT " + selectString + " " +
            "FROM " + fromString;

        if (whereString != null) {
            queryString += " WHERE " + whereString;
        }

        // Create GROUP BY query string.
        // This seems unnecessarily complicated - isn't there always a GROUP BY clause?
        // Okay, not with continuous data, but still.
        // Continuous probably requires a different approach.  OS August 22.
        if (!cont.equals("1")) {
            ResultSet rs_6 = statement.executeQuery(
                QueryGenerator.createMetaQueriesExtractionQuery(
                    rchain,
                    "Counts",
                    "GROUPBY",
                    null,
                    false
                )
            );

            List<String> columns = extractEntries(rs_6, "Entries");
            String GroupByString = String.join(", ", columns);

            if (!GroupByString.isEmpty()) {
                queryString = queryString + " GROUP BY "  + GroupByString;
            }
        }

        return queryString;
    }


    /**
     * Generate the "_counts" table for the given RChain.
     *
     * @param dbTargetName - name of the database to create the "_counts" table in.
     * @param shortRchain - the short form name of the RChain.
     * @param storageEngine - the storage engine to use for the tables created when executing this method.
     * @param countsTableSubQuery - subquery that retrieves the counts information.
     * @return the name of the "_counts" table generated.
     * @throws SQLException if an error occurs when executing the queries.
     */
    public static String generateCountsTable(
        String dbTargetName,
        String shortRchain,
        String storageEngine,
        String countsTableSubQuery
    ) throws SQLException {
        String tableName = shortRchain + "_counts";
        dbConnection.setCatalog(dbTargetName);
        try (Statement statement = dbConnection.createStatement()) {
            String createString = QueryGenerator.createSimpleCreateTableQuery(
                tableName,
                storageEngine,
                countsTableSubQuery
            );

            statement.executeUpdate("SET tmp_table_size = " + dbTemporaryTableSize + ";");
            statement.executeUpdate("SET max_heap_table_size = " + dbTemporaryTableSize + ";");
            statement.executeUpdate(createString);
        }

        return tableName;
    }


    /**
     * Create the "_counts" table for the given RChain, extracting the information necessary to generate a partial
     * dependency plot (PDP) for doing table JOINs.
     *
     * @param dbTargetName - name of the database to create the "_counts" table in.
     * @param shortRchain - the short form name of the RChain.
     * @param storageEngine - the storage engine to use for the tables created when executing this method.
     * @param subQueryDetails - {@code String[]} containing the query for creating the "_counts" table (String[0]), the
     *                          table references of the FROM clause in the given query (String[1]), and the conditions
     *                          for the WHERE clause in the given query (String[2]).
     * @return the name of the "_counts" table generated.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static String generateCountsTableAndPDPInfo(
        String dbTargetName,
        String shortRchain,
        String storageEngine,
        String[] subQueryDetails
    ) throws SQLException {
        String countsTableSubQuery = subQueryDetails[0];
        String fromTables = subQueryDetails[1];
        String whereConditions = subQueryDetails[2];
        String parameters = extractJoinPDPInfo(fromTables, whereConditions);
        long start = System.currentTimeMillis();

        String tableName = generateCountsTable(
            dbTargetName,
            shortRchain,
            storageEngine,
            countsTableSubQuery
        );

        RuntimeLogger.pdpOutput(
            logger,
            "Counts Build Time",
            parameters,
            start,
            System.currentTimeMillis()
        );

        return tableName;
    }


    /**
     * Extract the parameters of interest to generate partial dependency plots (PDPs) for JOINing database tables.
     *
     * @param fromTables - CSV of table aliases for the FROM clause to generate an "_counts" table.
     * @param whereConditions - equality conditions for the WHERE clause to generate an "_counts" table.
     * @return CSV of the parameters used to generate PDPs for JOINing database tables.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static String extractJoinPDPInfo(
        String fromTables,
        String whereConditions
    ) throws SQLException {
        if (relationTables == null) {
            // Retrieve the names of all the relationship tables.
            relationTables = retrieveRelationTables();
        }

        // Map the aliases to their true database table name.
        Map<String, String> tableAliases = mapAliases(fromTables);

        int maxR = 0;
        BigDecimal avgD = new BigDecimal(0);
        BigDecimal maxD = new BigDecimal(0);
        Set<String> rtables = new HashSet<String>();
        String[] equalities = whereConditions.split(AND_SEPARATOR);

        // for loop to process all the equalities.
        for (String equality : equalities) {
            // for loop to process the left and right sides of the equality.
            for (String equalityComponent : equality.split(" = ")) {
                String[] tableColRef = equalityComponent.split("\\.");
                String tableAlias = tableColRef[0];
                String databaseTable = tableAliases.get(tableAlias);
                if (relationTables.contains(tableAlias)) {
                    // If the table reference is a relationship table, then compute the degree information.
                    BigDecimal[] degreeInfo = computeDegree(databaseTable, tableColRef[1]);
                    avgD = avgD.max(degreeInfo[0]);
                    maxD = maxD.max(degreeInfo[1]);
                    rtables.add(tableAlias);
                } else {
                    // If the table reference is an entity table, then get the total number of rows in the table.
                    maxR = Math.max(maxR, countRows(databaseTable));
                }
            }
        }

        return "d" + avgD + ",D" + maxD + ",R" + maxR + ",t" + rtables.size();
    }


    /**
     * Determine the average and max degree of the entries in the given table for the specified column.
     *
     * @param table - name of the table to get the degree information from.
     * @param column - the column in the given table to get the degree information for.
     * @return {@code BigDecimal[]} containing the average degree (BigDecimal[0]) and the max degree (BigDecimal[1]).
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static BigDecimal[] computeDegree(String table, String column) throws SQLException {
        String degreeQuery =
            "SELECT " +
                "AVG(TOTAL) AS AVG, " +
                "MAX(TOTAL) AS MAX " +
            "FROM (" +
                "SELECT " +
                    column + ", " +
                    "COUNT(*) AS TOTAL " +
                "FROM " +
                    table + " " +
                "GROUP BY " +
                    column +
            ") AS TABULATED;";

        try (
            Statement statement = dbConnection.createStatement();
            ResultSet results = statement.executeQuery(degreeQuery)
        ) {
            results.next();
            BigDecimal[] stats = new BigDecimal[2];
            stats[0] = results.getBigDecimal("AVG");
            stats[1] = results.getBigDecimal("MAX");

            return stats;
        }
    }


    /**
     * Get the row count for the given database table.
     *
     * @param databaseTable - name of the database table to get the row count for.
     * @return the number of rows in the given database table.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static int countRows(String databaseTable) throws SQLException {
        try (
            Statement statement = dbConnection.createStatement();
            ResultSet results = statement.executeQuery(
                "SELECT COUNT(*) AS TOTAL FROM " + databaseTable
            )
        ) {
            results.next();
            return results.getInt("TOTAL");
        }
    }


    /**
     * Retrieve the aliases for all the relationship tables in the input database.
     *
     * @return the aliases for all the relationship tables.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static Set<String> retrieveRelationTables() throws SQLException {
        Set<String> relationTableAliases = new HashSet<String>();
        dbConnection.setCatalog(dbInfo.getSetupDatabaseName());
        try (
            Statement statement = dbConnection.createStatement();
            ResultSet results = statement.executeQuery(
                "SELECT " +
                    "rnid " +
                "FROM " +
                    "RNodes"
            )
        ) {
            while(results.next()) {
                relationTableAliases.add("`" + results.getString("rnid") + "`");
            }
        }

        return relationTableAliases;
    }


    /**
     * Create a mapping from table aliases back to their original table name.
     *
     * @param aliases - CSV of table aliases.
     * @return {@code Map} containing key:value pairs alias:original-table-name.
     */
    private static Map<String, String> mapAliases(String aliases) {
        Map<String, String> aliasMapping = new HashMap<String, String>();

        for(String alias : aliases.split(CSV_SEPARATOR)) {
            String[] aliasComponents = alias.split(" AS ");
            aliasMapping.put(aliasComponents[1], aliasComponents[0]);
        }

        return aliasMapping;
    }


    /**
     * Create an SQL query to generate the star table for the given RNode.
     *
     * @param rnode - the name of the RNode to build the "_star" table for.
     * @param shortRNode - the short name of the RNode to build the "_star" table for.
     * @return an SQL query to generate the star table for the given RNode.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static String buildRNodeStarQuery(
        String rnode,
        String shortRNode
    ) throws SQLException {
        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        Statement statement = dbConnection.createStatement();

        // Create SELECT query string.
        String selectQuery = QueryGenerator.createMetaQueriesExtractionQuery(
            rnode,
            "Star",
            "SELECT",
            null,
            true
        );

        List<String> columns;
        try (ResultSet result = statement.executeQuery(selectQuery)) {
            columns = extractEntries(result, "Entries");
        }
        String selectString = String.join(", ", columns);

        // Create * query string, which will be used for the "SELECT AS MULT".
        String multiplicationQuery = QueryGenerator.createMetaQueriesExtractionQuery(
            rnode,
            "Star",
            "FROM",
            null,
            false
        );

        try (ResultSet result = statement.executeQuery(multiplicationQuery)) {
            columns = extractEntries(result, "Entries");
        }
        statement.close();
        String multiplicationString = makeStarSepQuery(columns);

        // Create FROM query string.
        String fromString = dbInfo.getCTDatabaseName() + "." + String.join(", " + dbInfo.getCTDatabaseName() + ".", columns);

        // Create the final query string.
        String queryString = "SELECT " + multiplicationString + " AS MULT";
        if (!selectString.isEmpty()) {
            queryString += ", " + selectString;
        }
        queryString += " FROM " + fromString;

        return queryString;
    }


    /**
     * Create the flat table for the given RNode.
     *
     * @param rnode - the name of the RNode to build the "_flat" table for.
     * @param shortRNode - the short name of the RNode to build the "_flat" table for.
     * @param storageEngine - the storage engine to use for the table created when executing this method.
     * @param countsTableSubQuery - subquery that retrieves the counts information.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static void buildRNodeFlat(
        String rnode,
        String shortRNode,
        String storageEngine,
        String countsTableSubQuery
    ) throws SQLException {
        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        Statement statement = dbConnection.createStatement();

        // Create SELECT query string.
        String selectQuery = QueryGenerator.createMetaQueriesExtractionQuery(
            rnode,
            "Flat",
            "SELECT",
            null,
            false
        );

        List<String> columns;
        try (ResultSet rs2 = statement.executeQuery(selectQuery)) {
            columns = extractEntries(rs2, "Entries");
        }
        String selectString = String.join(", ", columns);

        // Create FROM query string.
        String fromQuery = QueryGenerator.createMetaQueriesExtractionQuery(
            rnode,
            "Flat",
            "FROM",
            null,
            false
        );
        try (ResultSet result = statement.executeQuery(fromQuery)) {
            columns = extractEntries(result, "Entries");
        }
        String fromString = String.join(", ", columns);
        fromString = fromString.replaceFirst(
            "`" + shortRNode + "_counts`",
            "(" + countsTableSubQuery + ") AS " + shortRNode + "_counts"
        );

        // Create the final query string.
        String queryString = "SELECT " + selectString + " FROM " + fromString;

        // Create GROUP BY query string.
        if (!cont.equals("1")) {
            String groupByQuery = QueryGenerator.createMetaQueriesExtractionQuery(
                rnode,
                "Flat",
                "GROUPBY",
                null,
                false
            );
            try (ResultSet result = statement.executeQuery(groupByQuery)) {
                columns = extractEntries(result, "Entries");
            }
            String groupByString = String.join(", ", columns);
            if (!groupByString.isEmpty()) {
                queryString += " GROUP BY "  + groupByString;
            }
        }
        statement.close();

        String flatTableName = shortRNode + "_flat";
        String createString = QueryGenerator.createSimpleCreateTableQuery(
            flatTableName,
            storageEngine,
            queryString
        );
        RuntimeLogger.logExecutedQuery(logger, createString);
        dbConnection.setCatalog(dbInfo.getCTDatabaseName());
        try (Statement createStatement = dbConnection.createStatement()) {
            createStatement.executeUpdate(createString);
        }

        // Add covering index.
        addCoveringIndex(
            dbConnection,
            dbInfo.getCTDatabaseName(),
            flatTableName
        );
    }


    /**
     * Create an SQL query to generate the false table for the given RNode using the sort merge algorithm.
     *
     * @param starTableSubQuery - a subquery that generates the "_star" table used to create the "_false" table.
     * @param shortRNode - the short name of the RNode to build the "_false" table for.
     * @return an SQL query to generate the false table for the given RNode using the sort merge algorithm.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static String buildRNodeFalseQuery(String starTableSubQuery, String shortRNode) throws SQLException {
        // Computing the false table as the MULT difference between the matching rows of the star and flat tables.
        return Sort_merge3.sort_merge(
            dbConnection,
            dbInfo.getCTDatabaseName(),
            starTableSubQuery,
            shortRNode + "_flat"
        );
    }


    /**
     * Create the query for generating the CT table of the given RNode.  This is done by cross joining the "_false"
     * table with the associated JOIN (derived) table, and then having the result UNIONed with the proper "_counts"
     * table.
     *
     * @param shortRNode - the short name of the RNode to build the "_CT" table for.
     * @param joinTableQueries - {@code Map} to retrieve the associated query to create a derived JOIN table.
     * @return query that can be used to generate the CT table for the given RNode.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static String buildRNodeCTCreationQuery(
        String rnode,
        String shortRNode,
        Map<String, String> joinTableQueries
    ) throws SQLException {
        // Must specify the columns or there will be column mismatches when taking the UNION of the counts and false
        // tables.
        String columnQuery =
            "SELECT Entries " +
            "FROM MetaQueries " +
            "WHERE Lattice_Point = '" + rnode + "' " +
            "AND ClauseType = 'SELECT' " +
            "AND EntryType <> 'aggregate' " +
            "AND TableType = 'Counts';";

        // Extract and escape the column names since they look like function calls to MySQL.
        List<String> columns;
        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        try (
            Statement statement = dbConnection.createStatement();
            ResultSet result = statement.executeQuery(columnQuery)
        ) {
            columns = extractEntries(result, "Entries");
        }
        String UnionColumnString;
        if (columns.size() > 0) {
            UnionColumnString = "MULT, " + makeDelimitedString(columns, ", ", " AS ");
        } else {
            UnionColumnString = "MULT";
        }

        // Join the false table with the join table to introduce rnid (= F) and 2nids (= N/A).  Then union the result
        // with the counts table.
        String createCTString =
            "SELECT " + UnionColumnString + " " +
            "FROM (" + COUNTS_SUBQUERY_PLACEHOLDER + ") AS " + shortRNode + "_counts " +
            "WHERE MULT > 0 " +

            "UNION ALL " +

            "SELECT " + UnionColumnString + " " +
            "FROM " +
                "(" + FALSE_SUBQUERY_PLACEHOLDER + ") AS FALSE_TABLE, " +
                "(" + joinTableQueries.get(shortRNode) + ") AS JOIN_TABLE " +
            "WHERE MULT > 0";
        return createCTString;
    }


    /**
     * Create queries that can be used to create JOIN tables as derived tables in "FROM" clauses.
     * <p>
     * JOIN tables are used to help represent the case where a relationship is false and its attributes are undefined.
     * JOIN tables are cross joined with "_false" tables to help generate the "_CT" tables.
     * </p>
     * @return a {@code Map} object containing queries that can be used to create JOIN tables as derived tables.  The
     *         entries in the {@code Map} object have the form of &lt;short_rnid&gt;:&lt;joinTableQuery&gt;.
     * @throws SQLException if there are issues executing the SQL queries.
     */
    private static Map<String, String> createJoinTableQueries() throws SQLException {
        Map<String, String> joinTableQueries = new HashMap<String, String>();

        dbConnection.setCatalog(dbInfo.getBNDatabaseName());
        Statement st = dbConnection.createStatement();
        ResultSet rs = st.executeQuery("select orig_rnid, short_rnid from LatticeRNodes ;");

        while(rs.next()){
        //  get rnid
            String short_rnid = rs.getString("short_rnid");
            String orig_rnid = rs.getString("orig_rnid");

            Statement st2 = dbConnection.createStatement();

            //  create ColumnString
            ResultSet rs2 = st2.executeQuery(
                QueryGenerator.createMetaQueriesExtractionQuery(
                    orig_rnid,
                    "Join",
                    "COLUMN",
                    null,
                    false
                )
            );

            List<String> columns = extractEntries(rs2, "Entries");
            String additionalColumns = String.join(", ", columns);
            StringBuilder joinTableQuerybuilder = new StringBuilder("SELECT \"F\" AS `" + orig_rnid + "`");
            if (!additionalColumns.isEmpty()) {
                joinTableQuerybuilder.append(", " + additionalColumns);
            }

            joinTableQueries.put(short_rnid, joinTableQuerybuilder.toString());
            st2.close();
        }

        rs.close();
        st.close();

        return joinTableQueries;
    }


    /**
     * Extract the values from the specified column of the given {@code ResultSet}.
     *
     * @param results - the ResultSet to extract the values from the specified column.
     * @param column - the column to extract the values from.
     * @return the list of values in the specified column of the given {@code ResultSet}.
     * @throws SQLException if an error occurs when trying to extract the column values.
     */
    private static List<String> extractEntries(ResultSet results, String column) throws SQLException {
        ArrayList<String> values = new ArrayList<String>();
        while (results.next()) {
            values.add(results.getString(column));
        }

        return values;
    }


    /**
     * Generate the multiplication string between the columns necessary to generate an _star table.
     *
     * @param columns - the columns to multiply together.
     * @return the multiplication string between the columns necessary to generate an _star table.
     */
    private static String makeStarSepQuery(List<String> columns) {
        String[] parts = new String[columns.size()];
        int index = 0;
        for (String column : columns) {
            parts[index] = column + ".MULT";
            index++;
        }

        return String.join(" * ", parts);
    }


    /**
     * Generate an escaped, comma delimited list of columns to generate an _CT table.
     *
     * @param columns - the columns to escape using backticks "`" and make a CSV with.
     * @return an escaped, comma delimited list of columns to generate an _CT table.
     */
    private static String makeEscapedCommaSepQuery(List<String> columns) {
        StringJoiner escapedCSV = new StringJoiner("`, `", "`", "`");

        for (String column : columns) {
            escapedCSV.add(column);
        }

        return escapedCSV.toString();
    }


    /**
     * Method to help retrieve the alias names from the given SELECT aliases and concatenate them together using the
     * specified delimiter.
     * <p>
     * Example of what information is retrieved:
     * Professor AS Prof --> Prof
     * </p>
     * @param selectAliases - list of SELECT aliases to retrieve the alias names from.
     * @param delimiter - the delimiter to use when concatenating the alias names together.
     * @param aliasKeyword - the keyword (e.g. AS) used when generating SELECT alias statements.
     * @return the alias names from the given SELECT aliases separated by the specified delimiter.
     */
    private static String makeDelimitedString(List<String> selectAliases, String delimiter, String aliasKeyword) {
        String[] parts = new String[selectAliases.size()];
        int index = 0;
        for (String selectAlias : selectAliases) {
            int prefixDelimiterStartIndex = selectAlias.indexOf(aliasKeyword);
            int prefixDelimiterEndIndex = prefixDelimiterStartIndex + aliasKeyword.length();
            parts[index] = selectAlias.substring(prefixDelimiterEndIndex);
            index++;
        }

        return String.join(delimiter, parts);
    }


    /**
     * Add a covering index to the specified table.
     * <p>
     * Note: All columns will be part of the index except for the "MULT" column.  If there is only a "MULT" column in
     *       the table, no index will be created.
     * </p>
     *
     * @param dbConnection - connection to the database containing the table to create the covering index for.
     * @param databaseName - the name of the database that the specified table is located in.
     * @param tableName - the name of the table to add a covering index to.
     * @throws SQLException if an error occurs when executing the queries.
     */
    private static void addCoveringIndex(Connection dbConnection, String databaseName, String tableName) throws SQLException {
        String allColumnsQuery =
            "SELECT column_name " +
            "FROM information_schema.columns " +
            "WHERE table_schema = '" + databaseName + "' " +
            "AND table_name = '" + tableName + "';";

        try (
            Statement dbStatement = dbConnection.createStatement();
            ResultSet columnsResults = dbStatement.executeQuery(allColumnsQuery)
        ) {
            String columnsCSV = makeIndexQuery(columnsResults, "column_name", ", ");
            if (!columnsCSV.isEmpty()) {
                dbStatement.execute(
                    "ALTER TABLE `" + tableName + "` " +
                    "ADD INDEX CoveringIndex (" + columnsCSV + ");"
                );
            }
        }
    }


    /**
     * Making Index Query by adding "`" and appending ASC
     * @param rs
     * @param colName
     * @param del
     * @return
     * @throws SQLException
     */
    private static String makeIndexQuery(ResultSet rs, String colName, String del) throws SQLException {

        ArrayList<String> parts = new ArrayList<String>();
        int count=0;
        while(rs.next()&count<16){

                String temp =rs.getString(colName);
                if (temp.equals("MULT")) {
                    continue;
                }
                temp= "`"+temp+"`";
            parts.add(temp+ " ASC");
            count ++;
        }

        return String.join(del, parts);
    }


    /**
     * Interface to enable the ability to switch between using the
     * {@link CountsManager#generatePVarsCountsTable(String, String, List, String, String)}
     * method and the
     * {@link CountsManager#generatePVarsCountsTableFromCache(String, String, List, String, String)}
     * method.
     *
     * @param <A> (String) the name of the output database.
     * @param <B> (String) the name of the "_counts" table to generate.
     * @param <C> (List&lt;String&gt;) the alias statements for the columns.
     * @param <D> (String) the storage engine to use for the "_counts" table generated.
     * @param <E> (String) the population variable of the "_counts" table generated.
     * @param <F> (SQLException) the SQLException that should be thrown if there are issues executing the SQL queries.
     */
    @FunctionalInterface
    private interface GeneratePVarsCountsMethod<A, B, C extends List<String>, D, E, F extends SQLException> {
        public void apply(
            A outputDatabaseName,
            B outputTableName,
            C columnAliases,
            D storageEngine,
            E pvariable
        ) throws F;
    }


    /**
     * Interface to enable the ability to switch between using the
     * {@link CountsManager#buildRNodesCT(String, String, String, String, String, String)
     * method and the
     * {@link CountsManager#buildRNodesCTFromCache(String, String, String, String, String, String)
     * method.
     *
     * @param <A> (String) the name of the output database.
     * @param <B> (String) the name of the output table.
     * @param <C> (CountingStrategy) {@link CountingStrategy} to indicate how counts related tables should be
     *                               generated.
     * @param <D> (String) the SELECT query used to create the CT table.
     * @param <E> (String) the name of the RNode to generate the CT table for.
     * @param <F> (String) the short name of the RNode to generate the CT table for.
     * @param <G> (SQLException) the SQLException that should be thrown if there are issues executing the SQL queries.
     * @return True if the CT table was generated from a cache; otherwise false.
     */
    @FunctionalInterface
    private interface BuildRNodesCTMethod<A, B, C, D, E, F, G extends SQLException> {
        public boolean apply(
            A targetDatabaseName,
            B ctTableName,
            C countingStrategy,
            D ctCreationQuery,
            E rnode,
            F shortRNode
        ) throws G;
    }


    /**
     * Connect to all the relevant databases.
     *
     * @throws SQLException if there are issues connecting to the databases.
     */
    public static void connectDB() throws SQLException {
        dbConnection = connectDB(dbInfo.getBNDatabaseName());
    }


    /**
     * Disconnect from all the relevant databases.
     *
     * @throws SQLException if there are issues disconnecting from the databases.
     */
    public static void disconnectDB() throws SQLException {
        dbConnection.close();
    }
}