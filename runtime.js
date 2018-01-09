const { Pool, Client } = require('pg')

function makePool(db, user, host, password) {
    return new Pool({
        user: user,
        host: host,
        database: db,
        password: password
    });
}

var client = new Client();

function escapeIdentifier(ident) {
    return client.escapeIdentifier(ident);
}

function escapeLiteral(lit) {
    return client.escapeLiteral(lit);
}

function query(pool, query) {

    return eventGenerator(function(cb) {

        pool.query(query, (err, res) => {

            if(err) throw err;

            cb(res);

        });
    });
}
