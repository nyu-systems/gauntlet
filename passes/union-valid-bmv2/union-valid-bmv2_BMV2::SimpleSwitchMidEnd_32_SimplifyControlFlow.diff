--- before_pass
+++ after_pass
@@ -44,10 +44,8 @@ control egress(inout Headers h, inout Me
 control deparser(packet_out b, in Headers h) {
     apply {
         b.emit<Hdr1>(h.h1);
-        {
-            b.emit<Hdr1>(h.u.h1);
-            b.emit<Hdr2>(h.u.h2);
-        }
+        b.emit<Hdr1>(h.u.h1);
+        b.emit<Hdr2>(h.u.h2);
     }
 }
 control ingress(inout Headers h, inout Meta m, inout standard_metadata_t sm) {
@@ -64,10 +62,8 @@ control ingress(inout Headers h, inout M
         default_action = a_1();
     }
     apply {
-        {
-            key_0 = h.u.isValid();
-            t_0.apply();
-        }
+        key_0 = h.u.isValid();
+        t_0.apply();
     }
 }
 V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
