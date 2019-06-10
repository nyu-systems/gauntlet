--- before_pass
+++ after_pass
@@ -29,7 +29,7 @@ struct test_digest_t {
     macAddr_t in_mac_srcAddr;
 }
 struct metadata {
-    test_digest_t test_digest;
+    bit<48> _test_digest_in_mac_srcAddr0;
 }
 struct headers {
     ethernet_t ethernet;
@@ -95,8 +95,8 @@ control MyIngress(inout headers hdr, ino
         default_action = NoAction_1();
     }
     @name("MyIngress.send_digest") action send_digest() {
-        meta.test_digest.in_mac_srcAddr = hdr.ethernet.srcAddr;
-        digest<test_digest_t>(32w1, meta.test_digest);
+        meta._test_digest_in_mac_srcAddr0 = hdr.ethernet.srcAddr;
+        digest<test_digest_t>(32w1, test_digest_t {in_mac_srcAddr = meta._test_digest_in_mac_srcAddr0});
     }
     apply {
         ipv4_lpm_0.apply();
