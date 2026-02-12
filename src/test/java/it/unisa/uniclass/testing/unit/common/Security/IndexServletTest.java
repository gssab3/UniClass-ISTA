package it.unisa.uniclass.testing.unit.common;

import it.unisa.uniclass.common.IndexServlet;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import it.unisa.uniclass.utenti.model.Utente;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.lang.reflect.Field;
import java.util.Arrays;
import java.util.List;

import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class IndexServletTest {

    // Sottoclasse per esporre i metodi protected senza cambiare la firma (no throws extra)
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

    @Mock private HttpServletRequest request;
    @Mock private HttpServletResponse response;
    @Mock private HttpSession session;
    @Mock private RequestDispatcher dispatcher;
    @Mock private CorsoLaureaService corsoLaureaService;

    @BeforeEach
    void setUp() throws Exception {
        servlet = new TestableIndexServlet();

        // Iniezione del service privato tramite Reflection
        Field field = IndexServlet.class.getDeclaredField("corsoLaureaService");
        field.setAccessible(true);
        field.set(servlet, corsoLaureaService);
    }

    @Test
    @DisplayName("doGet: Redirect a Login se la sessione è null")
    void testDoGet_SessionNull() throws Exception {
        when(request.getSession(false)).thenReturn(null);

        servlet.doGet(request, response);

        verify(response).sendRedirect("Login.jsp");
        verifyNoInteractions(corsoLaureaService);
    }

    @Test
    @DisplayName("doGet: Redirect a Login se l'utente non è in sessione")
    void testDoGet_UserNullInSession() throws Exception {
        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("currentSessionUser")).thenReturn(null);

        servlet.doGet(request, response);

        verify(response).sendRedirect("Login.jsp");
    }

    @Test
    @DisplayName("doGet: Successo - Utente loggato carica i corsi e va alla index")
    void testDoGet_Success() throws Exception {
        // Arrange
        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("currentSessionUser")).thenReturn(new Utente());

        List<CorsoLaurea> corsiMock = Arrays.asList(new CorsoLaurea("Informatica"), new CorsoLaurea("Fisica"));
        when(corsoLaureaService.trovaTutti()).thenReturn(corsiMock);

        when(request.getRequestDispatcher("index.jsp")).thenReturn(dispatcher);

        // Act
        servlet.doGet(request, response);

        // Assert
        verify(request).setAttribute("corsi", corsiMock);
        verify(dispatcher).forward(request, response);
    }

    @Test
    @DisplayName("doGet: Gestione Eccezione Service (Errore 500)")
    void testDoGet_ExceptionHandling() throws Exception {
        // Arrange
        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("currentSessionUser")).thenReturn(new Utente());
        when(corsoLaureaService.trovaTutti()).thenThrow(new RuntimeException("DB Error"));

        // Act
        servlet.doGet(request, response);

        // Assert
        verify(response).sendError(HttpServletResponse.SC_INTERNAL_SERVER_ERROR);
    }

    @Test
    @DisplayName("doPost: Deve delegare a doGet")
    void testDoPost_Delegation() {
        // Mock minimo per far passare il doGet senza errori fino al redirect
        when(request.getSession(false)).thenReturn(null);

        servlet.doPost(request, response);

        // Verifica che doGet sia stato effettivamente eseguito (controllo sul redirect)
        try {
            verify(response).sendRedirect("Login.jsp");
        } catch (Exception e) {
            e.printStackTrace();
        }
    }
}