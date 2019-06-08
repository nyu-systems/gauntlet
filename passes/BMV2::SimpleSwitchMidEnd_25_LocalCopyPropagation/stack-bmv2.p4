--- before_pass
+++ after_pass
@@ -32,10 +32,8 @@ control deparser(packet_out b, in Header
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
-    hdr[1] c_tmp_0;
     apply {
-        c_tmp_0[0].f = h.h.f + 32w1;
-        h.h.f = c_tmp_0[0].f;
+        h.h.f = h.h.f + 32w1;
         sm.egress_spec = 9w0;
     }
 }
