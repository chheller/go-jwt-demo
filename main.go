package main

import (
	"context"
	"crypto"
	"crypto/rsa"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"encoding/base64"
	"encoding/json"
	"encoding/pem"
	"errors"
	"fmt"
	"io"
	"log"
	"net/http"
	"os/signal"
	"strings"
	"syscall"
	"time"
)

// This is a bit of a hack due to Go getting a TLS Handshake timeout when using the http.DefaultClient
var client = &http.Client{
	Timeout: 20 * time.Second,
	Transport: &http.Transport{
		TLSHandshakeTimeout: 10 * time.Second,
		TLSClientConfig: &tls.Config{
			MinVersion: tls.VersionTLS12,
			CipherSuites: []uint16{
				tls.TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
				tls.TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
				tls.TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
				tls.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
			},
		},
	},
}

// Setup some basic application error types
var ErrApplicationGeneric = errors.New("application error")
var ErrTokenValidation = fmt.Errorf("%w: token validation error", ErrApplicationGeneric)

// Create a cache for public keys for each key id. We can cache these for the life time of the certificate
type KeyCacheEntry struct {
	Value     *x509.Certificate
	ExpiresAt time.Time
}

var publicKeyCache map[string]*KeyCacheEntry = map[string]*KeyCacheEntry{}

// Given a `kid` property from a JWT, go to the issuer and fetch the public key which the JWT was signed with.
// Always aggressively cache this call, as the point of stateless JWTs is that you don't depend directly on the Authorization
// Server to authenticate every request. Be aware of public key changes and have a plan to invalidate the cache. In this example
// We use an in-memory cache, so simply restarting the process will invalidate the cache. Do not ever hardcode a public key.
// Avoid using configuration properties for public keys as well, as they are dynamic and can be easily fetched as needed via REST API
func getPublicKey(keyid string) (cert *x509.Certificate, err error) {
	cacheEntry := publicKeyCache[keyid]
	if cacheEntry != nil && time.Now().Before(cacheEntry.ExpiresAt) {
		log.Printf("Serving key id %s from cache", keyid)
		return publicKeyCache[keyid].Value, nil
	}
	log.Printf("Cache miss for key id %s", keyid)

	resp, err := client.Get(fmt.Sprintf("https://authorization-server.com/ext/oauth/x509/kid?v=%s", keyid))
	if err != nil {
		err = fmt.Errorf("%w: Error getting public key for keyid %s: %w", ErrTokenValidation, keyid, err)
		return
	}
	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return nil, fmt.Errorf("%w: Error getting public key for keyid %s: %w", ErrTokenValidation, keyid, err)
	}

	x509EncodedCert, _ := pem.Decode(body)
	if x509EncodedCert == nil {
		log.Printf("Failed to parse certificate %s", x509EncodedCert)
		err = fmt.Errorf("%w: Failed to decode PEM certificate", ErrTokenValidation)
		return
	}
	cert, err = x509.ParseCertificate(x509EncodedCert.Bytes)
	if err != nil {
		err = fmt.Errorf("%w: Failed to parse public signing key certificate: %w", ErrTokenValidation, err)
		return
	}

	publicKeyCache[keyid] = &KeyCacheEntry{
		Value:     cert,
		ExpiresAt: cert.NotAfter,
	}

	return cert, nil

}

// Decode, Validate, and return a parsed map of JWT Claims
func decodeJwt(rawJwtStr string) (header map[string]any, payload map[string]any, err error) {

	// First we must slice the JWT up into its three constituent parts: the header JSON, the payload JSON, and the signature
	tokenSlice := strings.Split(rawJwtStr, ".")
	if len(tokenSlice) != 3 {
		err = fmt.Errorf("%w: Expected token to have three parts", ErrTokenValidation)
		return
	}
	headerBuf, err := base64.RawURLEncoding.DecodeString(tokenSlice[0])
	if err != nil {
		err = fmt.Errorf("%w: failed to parse header: %w", ErrTokenValidation, err)
		return
	}
	payloadBuf, err := base64.RawURLEncoding.DecodeString(tokenSlice[1])
	if err != nil {
		err = fmt.Errorf("%w: failed to parse payload: %w", ErrTokenValidation, err)
		return
	}
	// The signature is base64UrlEncoded, but is not JSON so we can leave it as a raw byte slice
	signature, err := base64.RawURLEncoding.DecodeString(tokenSlice[2])
	if err != nil {
		err = fmt.Errorf("%w: failed to parse signature: %w", ErrTokenValidation, err)
		return
	}
	// Marshal the header and payload from string JSON into generic maps of claims we can query later
	if err = json.Unmarshal(headerBuf, &header); err != nil {
		err = fmt.Errorf("%w: failed to parse header: %w", ErrTokenValidation, err)
		return
	}
	if err = json.Unmarshal(payloadBuf, &payload); err != nil {
		err = fmt.Errorf("%w: failed to parse payload: %w", ErrTokenValidation, err)
		return
	}

	// Validate token properties: algorithm, kid, exp, nbf, etf. Ideally we should also verify the client_id, aud, and iss
	if header["alg"].(string) != "RS256" {
		err = fmt.Errorf("%w: Unsupported algorithm '%s' expected RS256", ErrTokenValidation, header["alg"])
		return
	}
	if header["kid"] == nil {
		err = fmt.Errorf("%w: Missing kid parameter", ErrTokenValidation)
		return
	}

	nbf := int64(payload["nbf"].(float64))
	if nbf == 0 {
		err = fmt.Errorf("%w: Failed to parse nbf: %w", ErrTokenValidation, err)
		return
	}
	exp := int64(payload["exp"].(float64))
	if exp == 0 {
		err = fmt.Errorf("%w: Failed to parse exp: %w", ErrTokenValidation, err)
		return
	}
	expiry, notBefore := time.Unix(exp, 0), time.Unix(nbf, 0)

	// Ensure the token is valid by checking that the time is between Not Before and Expiry
	if !time.Now().Before(expiry) || !time.Now().After(notBefore) {
		err = fmt.Errorf("%w: Expected token to be valid after %s and before %s", ErrTokenValidation, notBefore, expiry)
		return
	}

	// Now we validate the signature itself, since this is the most expensive part we save it for the end as it is faster
	// to fail with less expensive validations

	// Combine the first two parts of the Base64UrlEncoded token with a period, as this is the data that was originally signed
	tokenPayloadBytes := strings.Join(tokenSlice[:2], ".")
	// Create a SHA256 Digest (note, this is different than a SHA256 HMAC, which uses a secret key)
	tokenHash := sha256.Sum256([]byte(tokenPayloadBytes))

	cert, err := getPublicKey(header["kid"].(string))

	if err != nil {
		return
	}

	// Use the retrieved RSA Public Key, the hashed payload, and the token's signature to verify the token itself.
	err = rsa.VerifyPKCS1v15(cert.PublicKey.(*rsa.PublicKey), crypto.SHA256, tokenHash[:], signature)
	if err != nil {
		err = fmt.Errorf("%w: Failed to verify token signature: %w", ErrTokenValidation, err)
		return
	}

	// If the token is valid, we can return the previously set header and payload maps
	return

}

// Boilerplate for adding Context Values
type key string

var userKey key

// Create a middleware for checking all incoming requests for an Authorization cookie
// attaches a Context Value to the request Context containing the user's id
func Authorizing(next http.Handler) http.Handler {
	return http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		cookie, err := r.Cookie("Authorization")

		// Check if the Authorization cookie is present, if not return unauthorized
		if err != nil || len(cookie.Value) == 0 {
			log.Print("Request missing Authorization header")
			w.WriteHeader(http.StatusUnauthorized)
			w.Write([]byte("Unauthorized"))
			return
		}
		// Validate and decode the JWT. If the token isn't valid, return unauthorized
		_, payload, err := decodeJwt(cookie.Value)
		if err != nil {
			log.Printf("%v", err)
			w.WriteHeader(http.StatusUnauthorized)
			w.Write([]byte("Unauthorized"))
			return
		}
		userId := payload["userid"].(string)
		if len(userId) == 0 {
			log.Printf("Expected userid to be defined, but got empty string")
		}

		// Add the properties from the token we're interested in to our Context. For this example we'll just use userid.
		// However, you might keep the access token itself to propagate to other services (such as the IDP to fetch a detailed user profile)
		log.Printf("Adding user with token %s to context", payload)
		ctx := context.WithValue(r.Context(), userKey, userId)
		next.ServeHTTP(w, r.WithContext(ctx))
	})
}

func main() {
	log.Println("Initializing application")
	router := http.NewServeMux()

	// Create a simple handler that returns a hello world message to the user
	router.HandleFunc("GET /hello-world", func(w http.ResponseWriter, r *http.Request) {
		w.WriteHeader(http.StatusOK)
		w.Write([]byte(fmt.Sprintf("Hello, %s!", r.Context().Value(userKey))))
	})

	server := http.Server{
		Addr: ":8080",
		// Wrap our ServeMux with our Authorization middleware
		Handler: Authorizing(router),
	}

	log.Println("Starting Server")

	// Create a context to hold the process open until it receives a SIGINT or SIGTERM signal from the OS
	ctx, stop := signal.NotifyContext(context.Background(), syscall.SIGINT, syscall.SIGTERM)
	defer stop()
	go func() {
		log.Printf("Server listening on %s", server.Addr)
		if err := server.ListenAndServe(); err != nil && !errors.Is(err, http.ErrServerClosed) {
			log.Fatalf("listen and serve returned err: %v", err)
		}
	}()

	// Wait until we get a signal to stop, keeping the tcp server open and accepting requests.
	<-ctx.Done()
	log.Println("got interruption signal")
	if err := server.Shutdown(context.TODO()); err != nil {
		log.Printf("server shutdown returned an err: %v\n", err)
	}
}
