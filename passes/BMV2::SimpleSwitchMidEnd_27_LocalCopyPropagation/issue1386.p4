--- before_pass
+++ after_pass
@@ -32,16 +32,14 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    bit<8> c_n;
     bool c_hasReturned;
     apply {
         {
             c_hasReturned = false;
-            c_n = 8w0;
             if (!h.h.isValid()) 
                 c_hasReturned = true;
             if (!c_hasReturned) 
-                if (c_n > 8w0) 
+                if (8w0 > 8w0) 
                     h.h.setValid();
         }
         sm.egress_spec = 9w0;
