--- before_pass
+++ after_pass
@@ -34,13 +34,9 @@ control deparser(packet_out b, in Header
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
     bool c_hasReturned_0;
     apply {
-        {
-            c_hasReturned_0 = false;
-            if (!h.h.isValid()) 
-                c_hasReturned_0 = true;
-            if (!c_hasReturned_0) 
-                ;
-        }
+        c_hasReturned_0 = false;
+        if (!h.h.isValid()) 
+            c_hasReturned_0 = true;
         sm.egress_spec = 9w0;
     }
 }
