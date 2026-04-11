import Lexicon.Annotation

/-!
# AnnotationTable
Entry point for holding user-authored annotations as an NSID-keyed table.
-/

namespace Lexicon

def timelineRead : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "feedViewPost[]"

def sessionRead : Annotation where
  requires := .capability "access_jwt"
  touches := .and (.emitCapability "access_jwt") (.emitSelf "actor")

def sessionInspect : Annotation where
  requires := .capability "access_jwt"
  touches := .and sessionRead.touches (.emitDatum "sessionView")

def sessionDelete : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "sessionDeleted"

def profilesRead : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "profileViewDetailed[]"

def authorFeedRead : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "authorFeedViewPost[]"

def feedRead : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "customFeedViewPost[]"

def postThreadRead : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "postThreadView"

def recordCreate : Annotation where
  requires := .and (.capability "access_jwt") (.ownershipSelf "actor")
  touches := .emitDatum "repoRecordCreated"

def recordDelete : Annotation where
  requires := .and (.capability "access_jwt") (.ownershipSelf "actor")
  touches := .emitDatum "repoRecordDeleted"

def notificationsRead : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "notification[]"

def notificationsSeen : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "notificationSeen"

def repoSubscription : Annotation where
  requires := .trivial
  touches := .emitDatum "repoCommitStream"

def demoAnnotationTable : List (String × Annotation) := [
  ("com.atproto.server.createSession", createSession),
  ("com.atproto.server.refreshSession", sessionRead),
  ("com.atproto.server.getSession", sessionInspect),
  ("com.atproto.server.deleteSession", sessionDelete),
  ("app.bsky.actor.getProfile", authSelfRead),
  ("app.bsky.actor.getProfiles", profilesRead),
  ("app.bsky.feed.getTimeline", timelineRead),
  ("app.bsky.feed.getAuthorFeed", authorFeedRead),
  ("app.bsky.feed.getFeed", feedRead),
  ("app.bsky.feed.getPostThread", postThreadRead),
  ("com.atproto.repo.createRecord", recordCreate),
  ("com.atproto.repo.deleteRecord", recordDelete),
  ("app.bsky.notification.listNotifications", notificationsRead),
  ("app.bsky.notification.updateSeen", notificationsSeen),
  ("com.atproto.sync.subscribeRepos", repoSubscription)
]

def demoNsids : List String :=
  demoAnnotationTable.map Prod.fst

example : demoAnnotationTable.length = 15 := by
  decide

end Lexicon
