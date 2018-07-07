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

    var cbs = []

    pool.query(query, function(err, result) {

        if(err) throw err;

        for(var i = 0; i < cbs.length; i++) {
            
            cbs[i](result)
        }
    });

    // Simulate native event
    return {
        on: function(name, cb) {
            cbs.push(cb)
        },
        removeListener: function(name, cb) {

            for(var i = 0; i < cbs.length; i++) {

                if(cbs[i] == cb) cbs.splice(i, 1)
            }
        }
    }

}




