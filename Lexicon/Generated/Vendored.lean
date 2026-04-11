import Lexicon.Basic

namespace Lexicon.Generated

def app_bsky_actor_getPreferences : Lexicon.LexiconCode := {
  nsid := "app.bsky.actor.getPreferences"
  kind := .query
  input := .object []
  output := .object [("preferences", .atom .token)]
}

def app_bsky_actor_getProfile : Lexicon.LexiconCode := {
  nsid := "app.bsky.actor.getProfile"
  kind := .query
  input := .object [("actor", .atom .token)]
  output := .atom .token
}

def app_bsky_actor_getProfiles : Lexicon.LexiconCode := {
  nsid := "app.bsky.actor.getProfiles"
  kind := .query
  input := .object [("actors", .array (.atom .token))]
  output := .object [("profiles", .array (.atom .token))]
}

def app_bsky_actor_getSuggestions : Lexicon.LexiconCode := {
  nsid := "app.bsky.actor.getSuggestions"
  kind := .query
  input := .object [("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("actors", .array (.atom .token)), ("recId", .atom .integer), ("recIdStr", .atom .string)]
}

def app_bsky_actor_putPreferences : Lexicon.LexiconCode := {
  nsid := "app.bsky.actor.putPreferences"
  kind := .procedure
  input := .object [("preferences", .atom .token)]
  output := .object []
}

def app_bsky_actor_searchActors : Lexicon.LexiconCode := {
  nsid := "app.bsky.actor.searchActors"
  kind := .query
  input := .object [("term", .atom .string), ("q", .atom .string), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("actors", .array (.atom .token))]
}

def app_bsky_actor_searchActorsTypeahead : Lexicon.LexiconCode := {
  nsid := "app.bsky.actor.searchActorsTypeahead"
  kind := .query
  input := .object [("term", .atom .string), ("q", .atom .string), ("limit", .atom .integer)]
  output := .object [("actors", .array (.atom .token))]
}

def app_bsky_feed_describeFeedGenerator : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.describeFeedGenerator"
  kind := .query
  input := .object []
  output := .object [("did", .atom .token), ("feeds", .array (.atom .token)), ("links", .atom .token)]
}

def app_bsky_feed_getActorFeeds : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getActorFeeds"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("feeds", .array (.atom .token))]
}

def app_bsky_feed_getActorLikes : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getActorLikes"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("feed", .array (.atom .token))]
}

def app_bsky_feed_getAuthorFeed : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getAuthorFeed"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string), ("filter", .atom .string), ("includePins", .atom .bool)]
  output := .object [("cursor", .atom .string), ("feed", .array (.atom .token))]
}

def app_bsky_feed_getFeed : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getFeed"
  kind := .query
  input := .object [("feed", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("feed", .array (.atom .token))]
}

def app_bsky_feed_getFeedGenerator : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getFeedGenerator"
  kind := .query
  input := .object [("feed", .atom .token)]
  output := .object [("view", .atom .token), ("isOnline", .atom .bool), ("isValid", .atom .bool)]
}

def app_bsky_feed_getFeedGenerators : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getFeedGenerators"
  kind := .query
  input := .object [("feeds", .array (.atom .token))]
  output := .object [("feeds", .array (.atom .token))]
}

def app_bsky_feed_getFeedSkeleton : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getFeedSkeleton"
  kind := .query
  input := .object [("feed", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("feed", .array (.atom .token)), ("reqId", .atom .string)]
}

def app_bsky_feed_getLikes : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getLikes"
  kind := .query
  input := .object [("uri", .atom .token), ("cid", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("uri", .atom .token), ("cid", .atom .token), ("cursor", .atom .string), ("likes", .array (.atom .token))]
}

def app_bsky_feed_getListFeed : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getListFeed"
  kind := .query
  input := .object [("list", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("feed", .array (.atom .token))]
}

def app_bsky_feed_getPostThread : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getPostThread"
  kind := .query
  input := .object [("uri", .atom .token), ("depth", .atom .integer), ("parentHeight", .atom .integer)]
  output := .object [("thread", .atom .token), ("threadgate", .atom .token)]
}

def app_bsky_feed_getPosts : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getPosts"
  kind := .query
  input := .object [("uris", .array (.atom .token))]
  output := .object [("posts", .array (.atom .token))]
}

def app_bsky_feed_getQuotes : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getQuotes"
  kind := .query
  input := .object [("uri", .atom .token), ("cid", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("uri", .atom .token), ("cid", .atom .token), ("cursor", .atom .string), ("posts", .array (.atom .token))]
}

def app_bsky_feed_getRepostedBy : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getRepostedBy"
  kind := .query
  input := .object [("uri", .atom .token), ("cid", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("uri", .atom .token), ("cid", .atom .token), ("cursor", .atom .string), ("repostedBy", .array (.atom .token))]
}

def app_bsky_feed_getSuggestedFeeds : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getSuggestedFeeds"
  kind := .query
  input := .object [("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("feeds", .array (.atom .token))]
}

def app_bsky_feed_getTimeline : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.getTimeline"
  kind := .query
  input := .object [("algorithm", .atom .string), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("feed", .array (.atom .token))]
}

def app_bsky_feed_searchPosts : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.searchPosts"
  kind := .query
  input := .object [("q", .atom .string), ("sort", .atom .string), ("since", .atom .string), ("until", .atom .string), ("mentions", .atom .token), ("author", .atom .token), ("lang", .atom .token), ("domain", .atom .string), ("url", .atom .token), ("tag", .array (.atom .string)), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("hitsTotal", .atom .integer), ("posts", .array (.atom .token))]
}

def app_bsky_feed_sendInteractions : Lexicon.LexiconCode := {
  nsid := "app.bsky.feed.sendInteractions"
  kind := .procedure
  input := .object [("feed", .atom .token), ("interactions", .array (.atom .token))]
  output := .object []
}

def app_bsky_graph_getActorStarterPacks : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getActorStarterPacks"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("starterPacks", .array (.atom .token))]
}

def app_bsky_graph_getBlocks : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getBlocks"
  kind := .query
  input := .object [("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("blocks", .array (.atom .token))]
}

def app_bsky_graph_getFollowers : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getFollowers"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("subject", .atom .token), ("cursor", .atom .string), ("followers", .array (.atom .token))]
}

def app_bsky_graph_getFollows : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getFollows"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("subject", .atom .token), ("cursor", .atom .string), ("follows", .array (.atom .token))]
}

def app_bsky_graph_getKnownFollowers : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getKnownFollowers"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("subject", .atom .token), ("cursor", .atom .string), ("followers", .array (.atom .token))]
}

def app_bsky_graph_getList : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getList"
  kind := .query
  input := .object [("list", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("list", .atom .token), ("items", .array (.atom .token))]
}

def app_bsky_graph_getListBlocks : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getListBlocks"
  kind := .query
  input := .object [("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("lists", .array (.atom .token))]
}

def app_bsky_graph_getListMutes : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getListMutes"
  kind := .query
  input := .object [("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("lists", .array (.atom .token))]
}

def app_bsky_graph_getLists : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getLists"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string), ("purposes", .array (.atom .string))]
  output := .object [("cursor", .atom .string), ("lists", .array (.atom .token))]
}

def app_bsky_graph_getListsWithMembership : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getListsWithMembership"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string), ("purposes", .array (.atom .string))]
  output := .object [("cursor", .atom .string), ("listsWithMembership", .array (.atom .token))]
}

def app_bsky_graph_getMutes : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getMutes"
  kind := .query
  input := .object [("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("mutes", .array (.atom .token))]
}

def app_bsky_graph_getRelationships : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getRelationships"
  kind := .query
  input := .object [("actor", .atom .token), ("others", .array (.atom .token))]
  output := .object [("actor", .atom .token), ("relationships", .array (.atom .token))]
}

def app_bsky_graph_getStarterPack : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getStarterPack"
  kind := .query
  input := .object [("starterPack", .atom .token)]
  output := .object [("starterPack", .atom .token)]
}

def app_bsky_graph_getStarterPacks : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getStarterPacks"
  kind := .query
  input := .object [("uris", .array (.atom .token))]
  output := .object [("starterPacks", .array (.atom .token))]
}

def app_bsky_graph_getStarterPacksWithMembership : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getStarterPacksWithMembership"
  kind := .query
  input := .object [("actor", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("starterPacksWithMembership", .array (.atom .token))]
}

def app_bsky_graph_getSuggestedFollowsByActor : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.getSuggestedFollowsByActor"
  kind := .query
  input := .object [("actor", .atom .token)]
  output := .object [("suggestions", .array (.atom .token)), ("recIdStr", .atom .string), ("isFallback", .atom .bool), ("recId", .atom .integer)]
}

def app_bsky_graph_muteActor : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.muteActor"
  kind := .procedure
  input := .object [("actor", .atom .token)]
  output := .object []
}

def app_bsky_graph_muteActorList : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.muteActorList"
  kind := .procedure
  input := .object [("list", .atom .token)]
  output := .object []
}

def app_bsky_graph_muteThread : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.muteThread"
  kind := .procedure
  input := .object [("root", .atom .token)]
  output := .object []
}

def app_bsky_graph_searchStarterPacks : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.searchStarterPacks"
  kind := .query
  input := .object [("q", .atom .string), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("starterPacks", .array (.atom .token))]
}

def app_bsky_graph_unmuteActor : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.unmuteActor"
  kind := .procedure
  input := .object [("actor", .atom .token)]
  output := .object []
}

def app_bsky_graph_unmuteActorList : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.unmuteActorList"
  kind := .procedure
  input := .object [("list", .atom .token)]
  output := .object []
}

def app_bsky_graph_unmuteThread : Lexicon.LexiconCode := {
  nsid := "app.bsky.graph.unmuteThread"
  kind := .procedure
  input := .object [("root", .atom .token)]
  output := .object []
}

def app_bsky_labeler_getServices : Lexicon.LexiconCode := {
  nsid := "app.bsky.labeler.getServices"
  kind := .query
  input := .object [("dids", .array (.atom .token)), ("detailed", .atom .bool)]
  output := .object [("views", .array (.atom .token))]
}

def app_bsky_notification_getPreferences : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.getPreferences"
  kind := .query
  input := .object []
  output := .object [("preferences", .atom .token)]
}

def app_bsky_notification_getUnreadCount : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.getUnreadCount"
  kind := .query
  input := .object [("priority", .atom .bool), ("seenAt", .atom .token)]
  output := .object [("count", .atom .integer)]
}

def app_bsky_notification_listActivitySubscriptions : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.listActivitySubscriptions"
  kind := .query
  input := .object [("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("subscriptions", .array (.atom .token))]
}

def app_bsky_notification_listNotifications : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.listNotifications"
  kind := .query
  input := .object [("reasons", .array (.atom .string)), ("limit", .atom .integer), ("priority", .atom .bool), ("cursor", .atom .string), ("seenAt", .atom .token)]
  output := .object [("cursor", .atom .string), ("notifications", .array (.atom .token)), ("priority", .atom .bool), ("seenAt", .atom .token)]
}

def app_bsky_notification_putActivitySubscription : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.putActivitySubscription"
  kind := .procedure
  input := .object [("subject", .atom .token), ("activitySubscription", .atom .token)]
  output := .object [("subject", .atom .token), ("activitySubscription", .atom .token)]
}

def app_bsky_notification_putPreferences : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.putPreferences"
  kind := .procedure
  input := .object [("priority", .atom .bool)]
  output := .object []
}

def app_bsky_notification_putPreferencesV2 : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.putPreferencesV2"
  kind := .procedure
  input := .object [("chat", .atom .token), ("follow", .atom .token), ("like", .atom .token), ("likeViaRepost", .atom .token), ("mention", .atom .token), ("quote", .atom .token), ("reply", .atom .token), ("repost", .atom .token), ("repostViaRepost", .atom .token), ("starterpackJoined", .atom .token), ("subscribedPost", .atom .token), ("unverified", .atom .token), ("verified", .atom .token)]
  output := .object [("preferences", .atom .token)]
}

def app_bsky_notification_registerPush : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.registerPush"
  kind := .procedure
  input := .object [("serviceDid", .atom .token), ("token", .atom .string), ("platform", .atom .string), ("appId", .atom .string), ("ageRestricted", .atom .bool)]
  output := .object []
}

def app_bsky_notification_unregisterPush : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.unregisterPush"
  kind := .procedure
  input := .object [("serviceDid", .atom .token), ("token", .atom .string), ("platform", .atom .string), ("appId", .atom .string)]
  output := .object []
}

def app_bsky_notification_updateSeen : Lexicon.LexiconCode := {
  nsid := "app.bsky.notification.updateSeen"
  kind := .procedure
  input := .object [("seenAt", .atom .token)]
  output := .object []
}

def app_bsky_video_getJobStatus : Lexicon.LexiconCode := {
  nsid := "app.bsky.video.getJobStatus"
  kind := .query
  input := .object [("jobId", .atom .string)]
  output := .object [("jobStatus", .atom .token)]
}

def app_bsky_video_getUploadLimits : Lexicon.LexiconCode := {
  nsid := "app.bsky.video.getUploadLimits"
  kind := .query
  input := .object []
  output := .object [("canUpload", .atom .bool), ("remainingDailyVideos", .atom .integer), ("remainingDailyBytes", .atom .integer), ("message", .atom .string), ("error", .atom .string)]
}

def app_bsky_video_uploadVideo : Lexicon.LexiconCode := {
  nsid := "app.bsky.video.uploadVideo"
  kind := .procedure
  input := .atom .token
  output := .object [("jobStatus", .atom .token)]
}

def com_atproto_identity_getRecommendedDidCredentials : Lexicon.LexiconCode := {
  nsid := "com.atproto.identity.getRecommendedDidCredentials"
  kind := .query
  input := .object []
  output := .object [("rotationKeys", .array (.atom .string)), ("alsoKnownAs", .array (.atom .string)), ("verificationMethods", .atom .token), ("services", .atom .token)]
}

def com_atproto_identity_refreshIdentity : Lexicon.LexiconCode := {
  nsid := "com.atproto.identity.refreshIdentity"
  kind := .procedure
  input := .object [("identifier", .atom .token)]
  output := .atom .token
}

def com_atproto_identity_requestPlcOperationSignature : Lexicon.LexiconCode := {
  nsid := "com.atproto.identity.requestPlcOperationSignature"
  kind := .procedure
  input := .object []
  output := .object []
}

def com_atproto_identity_resolveDid : Lexicon.LexiconCode := {
  nsid := "com.atproto.identity.resolveDid"
  kind := .query
  input := .object [("did", .atom .token)]
  output := .object [("didDoc", .atom .token)]
}

def com_atproto_identity_resolveHandle : Lexicon.LexiconCode := {
  nsid := "com.atproto.identity.resolveHandle"
  kind := .query
  input := .object [("handle", .atom .token)]
  output := .object [("did", .atom .token)]
}

def com_atproto_identity_resolveIdentity : Lexicon.LexiconCode := {
  nsid := "com.atproto.identity.resolveIdentity"
  kind := .query
  input := .object [("identifier", .atom .token)]
  output := .atom .token
}

def com_atproto_identity_signPlcOperation : Lexicon.LexiconCode := {
  nsid := "com.atproto.identity.signPlcOperation"
  kind := .procedure
  input := .object [("token", .atom .string), ("rotationKeys", .array (.atom .string)), ("alsoKnownAs", .array (.atom .string)), ("verificationMethods", .atom .token), ("services", .atom .token)]
  output := .object [("operation", .atom .token)]
}

def com_atproto_identity_submitPlcOperation : Lexicon.LexiconCode := {
  nsid := "com.atproto.identity.submitPlcOperation"
  kind := .procedure
  input := .object [("operation", .atom .token)]
  output := .object []
}

def com_atproto_identity_updateHandle : Lexicon.LexiconCode := {
  nsid := "com.atproto.identity.updateHandle"
  kind := .procedure
  input := .object [("handle", .atom .token)]
  output := .object []
}

def com_atproto_label_queryLabels : Lexicon.LexiconCode := {
  nsid := "com.atproto.label.queryLabels"
  kind := .query
  input := .object [("uriPatterns", .array (.atom .string)), ("sources", .array (.atom .token)), ("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("labels", .array (.atom .token))]
}

def com_atproto_moderation_createReport : Lexicon.LexiconCode := {
  nsid := "com.atproto.moderation.createReport"
  kind := .procedure
  input := .object [("reasonType", .atom .token), ("reason", .atom .string), ("subject", .atom .token), ("modTool", .atom .token)]
  output := .object [("id", .atom .integer), ("reasonType", .atom .token), ("reason", .atom .string), ("subject", .atom .token), ("reportedBy", .atom .token), ("createdAt", .atom .token)]
}

def com_atproto_repo_applyWrites : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.applyWrites"
  kind := .procedure
  input := .object [("repo", .atom .token), ("validate", .atom .bool), ("writes", .array (.atom .token)), ("swapCommit", .atom .token)]
  output := .object [("commit", .atom .token), ("results", .array (.atom .token))]
}

def com_atproto_repo_createRecord : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.createRecord"
  kind := .procedure
  input := .object [("repo", .atom .token), ("collection", .atom .token), ("rkey", .atom .token), ("validate", .atom .bool), ("record", .atom .token), ("swapCommit", .atom .token)]
  output := .object [("uri", .atom .token), ("cid", .atom .token), ("commit", .atom .token), ("validationStatus", .atom .string)]
}

def com_atproto_repo_deleteRecord : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.deleteRecord"
  kind := .procedure
  input := .object [("repo", .atom .token), ("collection", .atom .token), ("rkey", .atom .token), ("swapRecord", .atom .token), ("swapCommit", .atom .token)]
  output := .object [("commit", .atom .token)]
}

def com_atproto_repo_describeRepo : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.describeRepo"
  kind := .query
  input := .object [("repo", .atom .token)]
  output := .object [("handle", .atom .token), ("did", .atom .token), ("didDoc", .atom .token), ("collections", .array (.atom .token)), ("handleIsCorrect", .atom .bool)]
}

def com_atproto_repo_getRecord : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.getRecord"
  kind := .query
  input := .object [("repo", .atom .token), ("collection", .atom .token), ("rkey", .atom .token), ("cid", .atom .token)]
  output := .object [("uri", .atom .token), ("cid", .atom .token), ("value", .atom .token)]
}

def com_atproto_repo_importRepo : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.importRepo"
  kind := .procedure
  input := .atom .token
  output := .object []
}

def com_atproto_repo_listMissingBlobs : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.listMissingBlobs"
  kind := .query
  input := .object [("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("blobs", .array (.atom .token))]
}

def com_atproto_repo_listRecords : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.listRecords"
  kind := .query
  input := .object [("repo", .atom .token), ("collection", .atom .token), ("limit", .atom .integer), ("cursor", .atom .string), ("reverse", .atom .bool)]
  output := .object [("cursor", .atom .string), ("records", .array (.atom .token))]
}

def com_atproto_repo_putRecord : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.putRecord"
  kind := .procedure
  input := .object [("repo", .atom .token), ("collection", .atom .token), ("rkey", .atom .token), ("validate", .atom .bool), ("record", .atom .token), ("swapRecord", .atom .token), ("swapCommit", .atom .token)]
  output := .object [("uri", .atom .token), ("cid", .atom .token), ("commit", .atom .token), ("validationStatus", .atom .string)]
}

def com_atproto_repo_uploadBlob : Lexicon.LexiconCode := {
  nsid := "com.atproto.repo.uploadBlob"
  kind := .procedure
  input := .atom .token
  output := .object [("blob", .atom .token)]
}

def com_atproto_server_activateAccount : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.activateAccount"
  kind := .procedure
  input := .object []
  output := .object []
}

def com_atproto_server_checkAccountStatus : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.checkAccountStatus"
  kind := .query
  input := .object []
  output := .object [("activated", .atom .bool), ("validDid", .atom .bool), ("repoCommit", .atom .token), ("repoRev", .atom .string), ("repoBlocks", .atom .integer), ("indexedRecords", .atom .integer), ("privateStateValues", .atom .integer), ("expectedBlobs", .atom .integer), ("importedBlobs", .atom .integer)]
}

def com_atproto_server_confirmEmail : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.confirmEmail"
  kind := .procedure
  input := .object [("email", .atom .string), ("token", .atom .string)]
  output := .object []
}

def com_atproto_server_createAccount : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.createAccount"
  kind := .procedure
  input := .object [("email", .atom .string), ("handle", .atom .token), ("did", .atom .token), ("inviteCode", .atom .string), ("verificationCode", .atom .string), ("verificationPhone", .atom .string), ("password", .atom .string), ("recoveryKey", .atom .string), ("plcOp", .atom .token)]
  output := .object [("accessJwt", .atom .string), ("refreshJwt", .atom .string), ("handle", .atom .token), ("did", .atom .token), ("didDoc", .atom .token)]
}

def com_atproto_server_createAppPassword : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.createAppPassword"
  kind := .procedure
  input := .object [("name", .atom .string), ("privileged", .atom .bool)]
  output := .atom .token
}

def com_atproto_server_createInviteCode : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.createInviteCode"
  kind := .procedure
  input := .object [("useCount", .atom .integer), ("forAccount", .atom .token)]
  output := .object [("code", .atom .string)]
}

def com_atproto_server_createInviteCodes : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.createInviteCodes"
  kind := .procedure
  input := .object [("codeCount", .atom .integer), ("useCount", .atom .integer), ("forAccounts", .array (.atom .token))]
  output := .object [("codes", .array (.atom .token))]
}

def com_atproto_server_createSession : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.createSession"
  kind := .procedure
  input := .object [("identifier", .atom .string), ("password", .atom .string), ("authFactorToken", .atom .string), ("allowTakendown", .atom .bool)]
  output := .object [("accessJwt", .atom .string), ("refreshJwt", .atom .string), ("handle", .atom .token), ("did", .atom .token), ("didDoc", .atom .token), ("email", .atom .string), ("emailConfirmed", .atom .bool), ("emailAuthFactor", .atom .bool), ("active", .atom .bool), ("status", .atom .string)]
}

def com_atproto_server_deactivateAccount : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.deactivateAccount"
  kind := .procedure
  input := .object [("deleteAfter", .atom .token)]
  output := .object []
}

def com_atproto_server_deleteAccount : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.deleteAccount"
  kind := .procedure
  input := .object [("did", .atom .token), ("password", .atom .string), ("token", .atom .string)]
  output := .object []
}

def com_atproto_server_deleteSession : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.deleteSession"
  kind := .procedure
  input := .object []
  output := .object []
}

def com_atproto_server_describeServer : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.describeServer"
  kind := .query
  input := .object []
  output := .object [("inviteCodeRequired", .atom .bool), ("phoneVerificationRequired", .atom .bool), ("availableUserDomains", .array (.atom .string)), ("links", .atom .token), ("contact", .atom .token), ("did", .atom .token)]
}

def com_atproto_server_getAccountInviteCodes : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.getAccountInviteCodes"
  kind := .query
  input := .object [("includeUsed", .atom .bool), ("createAvailable", .atom .bool)]
  output := .object [("codes", .array (.atom .token))]
}

def com_atproto_server_getServiceAuth : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.getServiceAuth"
  kind := .query
  input := .object [("aud", .atom .token), ("exp", .atom .integer), ("lxm", .atom .token)]
  output := .object [("token", .atom .string)]
}

def com_atproto_server_getSession : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.getSession"
  kind := .query
  input := .object []
  output := .object [("handle", .atom .token), ("did", .atom .token), ("didDoc", .atom .token), ("email", .atom .string), ("emailConfirmed", .atom .bool), ("emailAuthFactor", .atom .bool), ("active", .atom .bool), ("status", .atom .string)]
}

def com_atproto_server_listAppPasswords : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.listAppPasswords"
  kind := .query
  input := .object []
  output := .object [("passwords", .array (.atom .token))]
}

def com_atproto_server_refreshSession : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.refreshSession"
  kind := .procedure
  input := .object []
  output := .object [("accessJwt", .atom .string), ("refreshJwt", .atom .string), ("handle", .atom .token), ("did", .atom .token), ("didDoc", .atom .token), ("email", .atom .string), ("emailConfirmed", .atom .bool), ("emailAuthFactor", .atom .bool), ("active", .atom .bool), ("status", .atom .string)]
}

def com_atproto_server_requestAccountDelete : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.requestAccountDelete"
  kind := .procedure
  input := .object []
  output := .object []
}

def com_atproto_server_requestEmailConfirmation : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.requestEmailConfirmation"
  kind := .procedure
  input := .object []
  output := .object []
}

def com_atproto_server_requestEmailUpdate : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.requestEmailUpdate"
  kind := .procedure
  input := .object []
  output := .object [("tokenRequired", .atom .bool)]
}

def com_atproto_server_requestPasswordReset : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.requestPasswordReset"
  kind := .procedure
  input := .object [("email", .atom .string)]
  output := .object []
}

def com_atproto_server_reserveSigningKey : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.reserveSigningKey"
  kind := .procedure
  input := .object [("did", .atom .token)]
  output := .object [("signingKey", .atom .string)]
}

def com_atproto_server_resetPassword : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.resetPassword"
  kind := .procedure
  input := .object [("token", .atom .string), ("password", .atom .string)]
  output := .object []
}

def com_atproto_server_revokeAppPassword : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.revokeAppPassword"
  kind := .procedure
  input := .object [("name", .atom .string)]
  output := .object []
}

def com_atproto_server_updateEmail : Lexicon.LexiconCode := {
  nsid := "com.atproto.server.updateEmail"
  kind := .procedure
  input := .object [("email", .atom .string), ("emailAuthFactor", .atom .bool), ("token", .atom .string)]
  output := .object []
}

def com_atproto_sync_getHostStatus : Lexicon.LexiconCode := {
  nsid := "com.atproto.sync.getHostStatus"
  kind := .query
  input := .object [("hostname", .atom .string)]
  output := .object [("hostname", .atom .string), ("seq", .atom .integer), ("accountCount", .atom .integer), ("status", .atom .token)]
}

def com_atproto_sync_listHosts : Lexicon.LexiconCode := {
  nsid := "com.atproto.sync.listHosts"
  kind := .query
  input := .object [("limit", .atom .integer), ("cursor", .atom .string)]
  output := .object [("cursor", .atom .string), ("hosts", .array (.atom .token))]
}

def com_atproto_sync_subscribeRepos : Lexicon.LexiconCode := {
  nsid := "com.atproto.sync.subscribeRepos"
  kind := .subscription
  input := .object [("cursor", .atom .integer)]
  output := .atom .token
}

def com_whtwnd_blog_getAuthorPosts : Lexicon.LexiconCode := {
  nsid := "com.whtwnd.blog.getAuthorPosts"
  kind := .query
  input := .object [("author", .atom .token)]
  output := .object [("post", .array (.atom .token))]
}

def com_whtwnd_blog_getEntryMetadataByName : Lexicon.LexiconCode := {
  nsid := "com.whtwnd.blog.getEntryMetadataByName"
  kind := .query
  input := .object [("author", .atom .token), ("entryTitle", .atom .string)]
  output := .object [("entryUri", .atom .token), ("lastUpdate", .atom .token), ("cid", .atom .token)]
}

def com_whtwnd_blog_getMentionsByEntry : Lexicon.LexiconCode := {
  nsid := "com.whtwnd.blog.getMentionsByEntry"
  kind := .query
  input := .object [("postUri", .atom .token)]
  output := .object [("mentions", .array (.atom .token))]
}

def com_whtwnd_blog_notifyOfNewEntry : Lexicon.LexiconCode := {
  nsid := "com.whtwnd.blog.notifyOfNewEntry"
  kind := .procedure
  input := .object [("entryUri", .atom .token)]
  output := .object []
}

def vendoredCodes : List Lexicon.LexiconCode := [
  app_bsky_actor_getPreferences,
  app_bsky_actor_getProfile,
  app_bsky_actor_getProfiles,
  app_bsky_actor_getSuggestions,
  app_bsky_actor_putPreferences,
  app_bsky_actor_searchActors,
  app_bsky_actor_searchActorsTypeahead,
  app_bsky_feed_describeFeedGenerator,
  app_bsky_feed_getActorFeeds,
  app_bsky_feed_getActorLikes,
  app_bsky_feed_getAuthorFeed,
  app_bsky_feed_getFeed,
  app_bsky_feed_getFeedGenerator,
  app_bsky_feed_getFeedGenerators,
  app_bsky_feed_getFeedSkeleton,
  app_bsky_feed_getLikes,
  app_bsky_feed_getListFeed,
  app_bsky_feed_getPostThread,
  app_bsky_feed_getPosts,
  app_bsky_feed_getQuotes,
  app_bsky_feed_getRepostedBy,
  app_bsky_feed_getSuggestedFeeds,
  app_bsky_feed_getTimeline,
  app_bsky_feed_searchPosts,
  app_bsky_feed_sendInteractions,
  app_bsky_graph_getActorStarterPacks,
  app_bsky_graph_getBlocks,
  app_bsky_graph_getFollowers,
  app_bsky_graph_getFollows,
  app_bsky_graph_getKnownFollowers,
  app_bsky_graph_getList,
  app_bsky_graph_getListBlocks,
  app_bsky_graph_getListMutes,
  app_bsky_graph_getLists,
  app_bsky_graph_getListsWithMembership,
  app_bsky_graph_getMutes,
  app_bsky_graph_getRelationships,
  app_bsky_graph_getStarterPack,
  app_bsky_graph_getStarterPacks,
  app_bsky_graph_getStarterPacksWithMembership,
  app_bsky_graph_getSuggestedFollowsByActor,
  app_bsky_graph_muteActor,
  app_bsky_graph_muteActorList,
  app_bsky_graph_muteThread,
  app_bsky_graph_searchStarterPacks,
  app_bsky_graph_unmuteActor,
  app_bsky_graph_unmuteActorList,
  app_bsky_graph_unmuteThread,
  app_bsky_labeler_getServices,
  app_bsky_notification_getPreferences,
  app_bsky_notification_getUnreadCount,
  app_bsky_notification_listActivitySubscriptions,
  app_bsky_notification_listNotifications,
  app_bsky_notification_putActivitySubscription,
  app_bsky_notification_putPreferences,
  app_bsky_notification_putPreferencesV2,
  app_bsky_notification_registerPush,
  app_bsky_notification_unregisterPush,
  app_bsky_notification_updateSeen,
  app_bsky_video_getJobStatus,
  app_bsky_video_getUploadLimits,
  app_bsky_video_uploadVideo,
  com_atproto_identity_getRecommendedDidCredentials,
  com_atproto_identity_refreshIdentity,
  com_atproto_identity_requestPlcOperationSignature,
  com_atproto_identity_resolveDid,
  com_atproto_identity_resolveHandle,
  com_atproto_identity_resolveIdentity,
  com_atproto_identity_signPlcOperation,
  com_atproto_identity_submitPlcOperation,
  com_atproto_identity_updateHandle,
  com_atproto_label_queryLabels,
  com_atproto_moderation_createReport,
  com_atproto_repo_applyWrites,
  com_atproto_repo_createRecord,
  com_atproto_repo_deleteRecord,
  com_atproto_repo_describeRepo,
  com_atproto_repo_getRecord,
  com_atproto_repo_importRepo,
  com_atproto_repo_listMissingBlobs,
  com_atproto_repo_listRecords,
  com_atproto_repo_putRecord,
  com_atproto_repo_uploadBlob,
  com_atproto_server_activateAccount,
  com_atproto_server_checkAccountStatus,
  com_atproto_server_confirmEmail,
  com_atproto_server_createAccount,
  com_atproto_server_createAppPassword,
  com_atproto_server_createInviteCode,
  com_atproto_server_createInviteCodes,
  com_atproto_server_createSession,
  com_atproto_server_deactivateAccount,
  com_atproto_server_deleteAccount,
  com_atproto_server_deleteSession,
  com_atproto_server_describeServer,
  com_atproto_server_getAccountInviteCodes,
  com_atproto_server_getServiceAuth,
  com_atproto_server_getSession,
  com_atproto_server_listAppPasswords,
  com_atproto_server_refreshSession,
  com_atproto_server_requestAccountDelete,
  com_atproto_server_requestEmailConfirmation,
  com_atproto_server_requestEmailUpdate,
  com_atproto_server_requestPasswordReset,
  com_atproto_server_reserveSigningKey,
  com_atproto_server_resetPassword,
  com_atproto_server_revokeAppPassword,
  com_atproto_server_updateEmail,
  com_atproto_sync_getHostStatus,
  com_atproto_sync_listHosts,
  com_atproto_sync_subscribeRepos,
  com_whtwnd_blog_getAuthorPosts,
  com_whtwnd_blog_getEntryMetadataByName,
  com_whtwnd_blog_getMentionsByEntry,
  com_whtwnd_blog_notifyOfNewEntry,
]

end Lexicon.Generated
