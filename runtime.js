const { Pool, Client } = require('pg')

function makePool(db, user, host, password) {
    return new Pool({
        user: user,
        host: host,
        database: db,
        password: password
    });
}

function query(pool, query) {

    return eventGenerator(function(cb) {

        pool.query(query, (err, res) => {

            if(err) throw err;

            cb(res);

        });
    });
}
