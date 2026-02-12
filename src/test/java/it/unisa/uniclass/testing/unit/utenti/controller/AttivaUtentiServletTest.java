package it.unisa.uniclass.testing.unit.utenti.controller;

import it.unisa.uniclass.utenti.controller.AttivaUtentiServlet;
import it.unisa.uniclass.utenti.model.Accademico;
import it.unisa.uniclass.utenti.model.Ruolo;
import it.unisa.uniclass.utenti.model.Utente;
import it.unisa.uniclass.utenti.service.UserDirectory;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.IOException;
import java.lang.reflect.Field;

import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class AttivaUtentiServletTest {

    // --- SOLUZIONE: Sottoclasse per esporre i metodi protected ---
    static class TestableAttivaUtentiServlet extends AttivaUtentiServlet {
        @Override
        public void doPost(HttpServletRequest req, HttpServletResponse resp) {
            super.doPost(req, resp);
        }

        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) {
            super.doGet(req, resp);
        }
    }

    private TestableAttivaUtentiServlet servlet;

    @Mock
    private HttpServletRequest request;

    @Mock
    private HttpServletResponse response;

    @Mock
    private ServletContext servletContext;

    @Mock
    private UserDirectory userDirectory;

    @BeforeEach
    void setUp() throws Exception {
        // Usiamo la versione Testable
        servlet = new TestableAttivaUtentiServlet();

        // Iniezione manuale del Mock @EJB via Reflection nella superclasse
        // Nota: Il campo 'userDirectory' è definito in AttivaUtentiServlet
        Field field = AttivaUtentiServlet.class.getDeclaredField("userDirectory");
        field.setAccessible(true);
        field.set(servlet, userDirectory);

        // Mock base
        lenient().when(request.getContextPath()).thenReturn("/ctx");
        lenient().when(request.getServletContext()).thenReturn(servletContext);
    }

    // --- TEST ACTION: ADD (Attivazione) ---

    @Test
    @DisplayName("Add Success: Utente trovato, ruolo e matricola corretti")
    void testAddSuccess() throws IOException {
        // Arrange
        String email = "studente@unisa.it";
        String matricola = "0512101111";

        when(request.getParameter("param")).thenReturn("add");
        when(request.getParameter("email")).thenReturn(email);
        when(request.getParameter("matricola")).thenReturn(matricola);
        when(request.getParameter("tipo")).thenReturn("STUDENTE");

        Accademico acc = new Accademico();
        acc.setEmail(email);
        acc.setMatricola(matricola);
        acc.setRuolo(Ruolo.STUDENTE);
        acc.setAttivato(false);

        when(userDirectory.getUser(email)).thenReturn(acc);

        // Act (Ora doPost è pubblico grazie alla sottoclasse)
        servlet.doPost(request, response);

        // Assert
        verify(userDirectory).updateProfile(acc);
        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp");
        assert acc.getPassword() != null : "La password dovrebbe essere generata";
        assert acc.isAttivato() : "L'utente dovrebbe essere attivato";
    }

    @Test
    @DisplayName("Add Error: Utente non trovato o null")
    void testAddError_UserNull() throws IOException {
        when(request.getParameter("param")).thenReturn("add");
        when(request.getParameter("email")).thenReturn("missing@unisa.it");

        when(userDirectory.getUser(anyString())).thenReturn(null);

        servlet.doPost(request, response);

        verify(userDirectory, never()).updateProfile(any());
        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp?action=error");
    }

    @Test
    @DisplayName("Add Error: Utente trovato ma non è un Accademico")
    void testAddError_NotAccademico() throws IOException {
        when(request.getParameter("param")).thenReturn("add");
        when(request.getParameter("email")).thenReturn("admin@unisa.it");

        Utente simpleUser = new Utente();
        when(userDirectory.getUser(anyString())).thenReturn(simpleUser);

        servlet.doPost(request, response);

        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp?action=error");
    }

    @Test
    @DisplayName("Add Error: Ruolo non corrispondente")
    void testAddError_WrongRole() throws IOException {
        when(request.getParameter("param")).thenReturn("add");
        when(request.getParameter("email")).thenReturn("prof@unisa.it");
        when(request.getParameter("tipo")).thenReturn("STUDENTE");

        Accademico acc = new Accademico();
        acc.setRuolo(Ruolo.DOCENTE);

        when(userDirectory.getUser(anyString())).thenReturn(acc);

        servlet.doPost(request, response);
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);

    }

    @Test
    @DisplayName("Add Error: Matricola non corrispondente")
    void testAddError_WrongMatricola() throws IOException {
        when(request.getParameter("param")).thenReturn("add");
        when(request.getParameter("email")).thenReturn("s@unisa.it");
        when(request.getParameter("matricola")).thenReturn("12345");
        when(request.getParameter("tipo")).thenReturn("STUDENTE");

        Accademico acc = new Accademico();
        acc.setRuolo(Ruolo.STUDENTE);
        acc.setMatricola("99999");

        when(userDirectory.getUser(anyString())).thenReturn(acc);

        servlet.doPost(request, response);

        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp?action=error");
    }

    // --- TEST ACTION: REMOVE (Disattivazione) ---

    @Test
    @DisplayName("Remove Success: Accademico trovato e disattivato")
    void testRemoveSuccess() throws IOException {
        when(request.getParameter("param")).thenReturn("remove");
        when(request.getParameter("email-remove")).thenReturn("target@unisa.it");

        Accademico acc = new Accademico();
        acc.setAttivato(true);

        when(userDirectory.getUser("target@unisa.it")).thenReturn(acc);

        servlet.doPost(request, response);

        verify(userDirectory).updateProfile(acc);
        assert !acc.isAttivato() : "L'utente dovrebbe essere disattivato";
        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp");
    }

    @Test
    @DisplayName("Remove: Utente non trovato (Nessuna azione)")
    void testRemove_UserNotFound() throws IOException {
        when(request.getParameter("param")).thenReturn("remove");
        when(request.getParameter("email-remove")).thenReturn("null@unisa.it");

        when(userDirectory.getUser(anyString())).thenReturn(null);

        servlet.doPost(request, response);

        verify(userDirectory, never()).updateProfile(any());
        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp");
    }

    @Test
    @DisplayName("Remove: Utente trovato ma non Accademico")
    void testRemove_NotAccademico() throws IOException {
        when(request.getParameter("param")).thenReturn("remove");
        when(request.getParameter("email-remove")).thenReturn("user@unisa.it");

        Utente u = new Utente();
        when(userDirectory.getUser(anyString())).thenReturn(u);

        servlet.doPost(request, response);

        verify(userDirectory, never()).updateProfile(any());
        verify(response).sendRedirect("/ctx/PersonaleTA/AttivaUtenti.jsp");
    }

    // --- TEST GENERICI ---

    @Test
    @DisplayName("DoGet delega a DoPost")
    void testDoGet() throws IOException {
        when(request.getParameter("param")).thenReturn("unknown");

        // Ora doGet è accessibile
        servlet.doGet(request, response);

        verifyNoInteractions(userDirectory);
    }

    @Test
    @DisplayName("Gestione Eccezioni: Log e 500")
    void testExceptionHandling() throws IOException {
        when(request.getParameter("param")).thenReturn("add");
        when(userDirectory.getUser(any())).thenThrow(new RuntimeException("DB Error"));

        servlet.doPost(request, response);

        verify(servletContext).log(contains("Error processing user activation"), any(RuntimeException.class));
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }
}