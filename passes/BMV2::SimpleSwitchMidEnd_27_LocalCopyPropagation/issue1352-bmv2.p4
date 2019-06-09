--- before_pass
+++ after_pass
@@ -96,7 +96,7 @@ control MyIngress(inout headers hdr, ino
     }
     @name("MyIngress.send_digest") action send_digest() {
         meta._test_digest_in_mac_srcAddr0 = hdr.ethernet.srcAddr;
-        digest<test_digest_t>(32w1, {meta._test_digest_in_mac_srcAddr0});
+        digest<test_digest_t>(32w1, {hdr.ethernet.srcAddr});
     }
     apply {
         ipv4_lpm_0.apply();
