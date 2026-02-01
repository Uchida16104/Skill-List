// Dafny Network Request/Response Verification

module NetworkHandling {
  datatype HttpMethod = GET | POST | PUT | DELETE
  datatype StatusCode = OK | Created | BadRequest | NotFound | ServerError

  datatype Request = Request(
    method: HttpMethod,
    path: string,
    body: string
  )

  datatype Response = Response(
    statusCode: StatusCode,
    body: string
  )

  predicate ValidPath(path: string) {
    |path| > 0 && path[0] == '/'
  }

  function StatusToCode(status: StatusCode): nat {
    match status
      case OK => 200
      case Created => 201
      case BadRequest => 400
      case NotFound => 404
      case ServerError => 500
  }

  method CreateSuccessResponse(body: string) returns (r: Response)
    ensures r.statusCode == OK
    ensures r.body == body
  {
    r := Response(OK, body);
  }

  method CreateErrorResponse(status: StatusCode, message: string) returns (r: Response)
    requires status != OK
    ensures r.statusCode == status
  {
    r := Response(status, message);
  }
}
