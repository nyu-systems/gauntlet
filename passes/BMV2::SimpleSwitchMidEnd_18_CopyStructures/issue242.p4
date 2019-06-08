--- before_pass
+++ after_pass
@@ -56,7 +56,9 @@ control Eg(inout Headers hdrs, inout Met
     @name("Eg.debug") register<bit<32>>(32w100) debug;
     @name("Eg.reg") register<bit<32>>(32w1) reg;
     @name("Eg.test") action test_0() {
-        val = { 32w0 };
+        {
+            val.field1 = 32w0;
+        }
         _pred = val.field1 != 32w0;
         if (_pred) 
             tmp_1 = 32w1;
