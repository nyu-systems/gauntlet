--- dumps/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_28_ValidateTableProperties.p4	2019-06-08 18:34:21.195570500 +0200
+++ dumps/pruned/union-valid-bmv2-BMV2::SimpleSwitchMidEnd_29_SimplifyControlFlow.p4	2019-06-08 18:34:21.265847500 +0200
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
         default_action = a_0();
     }
     apply {
-        {
-            key_0 = h.u.isValid();
-            t.apply();
-        }
+        key_0 = h.u.isValid();
+        t.apply();
     }
 }
 V1Switch<Headers, Meta>(p(), vrfy(), ingress(), egress(), update(), deparser()) main;
