Sql
============================

This Idris package tries to create a type safe interface to Postgresql. Currently only a small part of the SQL language is supported, but adding more functionality should be straightforward.

Usage
-----------------------------
Make sure to install the latest version of the Idris compiler. This package has a dependency on the [record\_](https://github.com/leon-vv/Record), [event](https://github.com/leon-vv/Event), [ferryjs](https://github.com/leon-vv/FerryJS) and effects packages. The effects package is bundled with the Idris compiler but the other packages should be installed manually. Then run:
```idris --install sql.ipkg```

To use the library when compiling a program type:
```idris -p effects -p record_ -p ferryjs -p event  Main.idr```

Documentation
----------------------------
```idris --mkdoc ./sql.ipkg```

License
----------------------------
Mozilla Public License, v. 2.0
