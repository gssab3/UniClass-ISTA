package it.unisa.uniclass.testing.unit.common.Security;

import it.unisa.uniclass.common.IndexServlet;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.utenti.model.Utente;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.util.List;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.*;

class IndexServletTest {

    // Sottoclasse solo per rendere pubblico doGet/doPost (se vuoi)
    static class TestableIndexServlet extends IndexServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) {
            super.doGet(req, resp);
        }

        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) {
            super.doPost(req, resp);
        }
    }

    private TestableIndexServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private CorsoLaureaService corsoLaureaService;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new TestableIndexServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        corsoLaureaService = mock(CorsoLaureaService.class);

        when(request.getRequestDispatcher("index.jsp")).thenReturn(dispatcher);

        // Iniezione del mock nel field @EJB tramite reflection
        Field f = IndexServlet.class.getDeclaredField("corsoLaureaService");
        f.setAccessible(true);
        f.set(servlet, corsoLaureaService);
    }

    @Test
    void testDoGet_userNotLogged_redirectsToLogin() throws Exception {
        when(request.getSession(false)).thenReturn(null);

        servlet.doGet(request, response);

        verify(response).sendRedirect("Login.jsp");
        verify(corsoLaureaService, never()).trovaTutti();
        verify(dispatcher, never()).forward(any(), any());
    }

    @Test
    void testDoGet_userLogged_successFlow() throws Exception {
        Utente user = new Utente();
        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("currentSessionUser")).thenReturn(user);

        List<CorsoLaurea> corsi = List.of(mock(CorsoLaurea.class));
        when(corsoLaureaService.trovaTutti()).thenReturn(corsi);

        servlet.doGet(request, response);

        verify(corsoLaureaService).trovaTutti();
        verify(request).setAttribute("corsi", corsi);
        verify(dispatcher).forward(request, response);
        verify(response, never()).sendError(anyInt());
    }

    @Test
    void testDoGet_serviceThrows_exceptionHandledAndSendError() throws Exception {
        Utente user = new Utente();
        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("currentSessionUser")).thenReturn(user);

        when(corsoLaureaService.trovaTutti()).thenThrow(new RuntimeException("DB error"));

        servlet.doGet(request, response);

        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
        verify(dispatcher, never()).forward(request, response);
    }

    @Test
    void testDoPost_delegatesToDoGet() throws Exception {
        Utente user = new Utente();
        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("currentSessionUser")).thenReturn(user);

        when(corsoLaureaService.trovaTutti()).thenReturn(List.of());

        servlet.doPost(request, response);

        verify(corsoLaureaService).trovaTutti();
        verify(dispatcher).forward(request, response);
    }
}
