--- before_pass
+++ after_pass
@@ -33,9 +33,10 @@ control deparser(packet_out b, in Header
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     bit<8> c_n_0;
+    bool c_hasReturned_0;
     apply {
         {
-            bool c_hasReturned_0 = false;
+            c_hasReturned_0 = false;
             c_n_0 = 8w0;
             if (!h.h.isValid()) 
                 c_hasReturned_0 = true;
