package ca.sfu.cs.factorbase.database;

import java.io.IOException;
import java.sql.DriverManager;
import java.sql.SQLException;
import java.text.MessageFormat;

import ca.sfu.cs.common.Configuration.Config;
import ca.sfu.cs.factorbase.exception.DataBaseException;
import ca.sfu.cs.factorbase.util.BZScriptRunner;

import com.mysql.jdbc.Connection;

public class MySQLFactorBaseDataBase implements FactorBaseDataBase {

    private static final String CONNECTION_STRING = "jdbc:{0}/{1}";
    private String baseDatabaseName;
    private Connection baseConnection;


    /**
     * Create connections to the databases required by FactorBase to learn a Bayesian Network.
     *
     * @param dbaddress - the address of the MySQL database to connect to. e.g. mysql://127.0.0.1
     * @param dbname - the name of the database with the original data. e.g. unielwin
     * @param username - the username to use when accessing the database.
     * @param password - the password to use when accessing the database.
     * @throws SQLException if there is a problem connecting to the required databases.
     */
    public MySQLFactorBaseDataBase(String dbaddress, String dbname, String username, String password) throws DataBaseException {
        this.baseDatabaseName = dbname;
        String baseConnectionString = MessageFormat.format(CONNECTION_STRING, dbaddress, dbname);

        try {
            this.baseConnection = (Connection) DriverManager.getConnection(baseConnectionString, username, password);
        } catch (SQLException e) {
            throw new DataBaseException("Unable to connect to the provided database.", e);
        }
    }


    @Override
    public void setupDatabase() throws DataBaseException {
        BZScriptRunner bzsr = new BZScriptRunner(this.baseDatabaseName, this.baseConnection);
        try {
            bzsr.runScript(Config.SCRIPTS_DIRECTORY + "setup.sql");
            bzsr.createSP(Config.SCRIPTS_DIRECTORY + "storedprocs.sql");
            bzsr.callSP("find_values");
        } catch (SQLException | IOException e) {
            throw new DataBaseException("An error occurred when attempting to setup the database for FactorBase.", e);
        }
    }
}
