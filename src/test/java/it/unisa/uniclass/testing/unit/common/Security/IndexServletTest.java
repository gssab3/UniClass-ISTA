package it.unisa.uniclass.testing.unit.common.Security;

import it.unisa.uniclass.common.IndexServlet;
import it.unisa.uniclass.orari.model.CorsoLaurea;
import it.unisa.uniclass.orari.service.CorsoLaureaService;
import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.mockito.MockedConstruction;

import javax.naming.Context;
import javax.naming.InitialContext;
import javax.naming.NameClassPair;
import javax.naming.NamingEnumeration;
import javax.naming.NamingException;
import java.io.IOException;
import java.lang.reflect.Method;
import java.util.List;

import static org.mockito.Mockito.*;

class IndexServletTest {

    // Sottoclasse per rendere pubblico il metodo protetto
    static class TestableIndexServlet extends IndexServlet {
        @Override
        public void doGet(HttpServletRequest req, HttpServletResponse resp) throws ServletException, IOException {
            super.doGet(req, resp);
        }
    }

    private TestableIndexServlet servlet;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private RequestDispatcher dispatcher;

    @BeforeEach
    void setUp() {
        servlet = new TestableIndexServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        dispatcher = mock(RequestDispatcher.class);

        when(request.getRequestDispatcher("index.jsp")).thenReturn(dispatcher);
        when(request.getContextPath()).thenReturn("/ctx");
        when(request.getServletContext()).thenReturn(mock(jakarta.servlet.ServletContext.class));
    }

    @Test
    void testDoGetSuccess_withJndiListingCovered() throws Exception {
        // 1) Mock costruttore di InitialContext per coprire la parte JNDI nel doGet
        // Costruiamo una enumeration con due elementi che causano ricorsione e poi eccezione (gestita)
        NamingEnumeration<NameClassPair> rootEnum = mock(NamingEnumeration.class);
        when(rootEnum.hasMore()).thenReturn(true, true, false);
        NameClassPair subctx = new NameClassPair("subctx", "javax.naming.Context");
        NameClassPair leaf = new NameClassPair("leaf", "java.lang.Object");
        when(rootEnum.next()).thenReturn(subctx, leaf);

        try (MockedConstruction<InitialContext> mockedInitial =
                     mockConstruction(InitialContext.class, (mockCtx, context) -> {
                         // java:global listing
                         when(mockCtx.list("java:global")).thenReturn(rootEnum);
                         // ricorsione: per i sotto-nodi lanciamo NamingException (verrà ignorata dal catch)
                         when(mockCtx.list("java:global/subctx")).thenThrow(new NamingException("not a context"));
                         when(mockCtx.list("java:global/leaf")).thenThrow(new NamingException("not a context"));
                     });
             // 2) Mock costruttore di CorsoLaureaService per pilotare il ramo success
             MockedConstruction<CorsoLaureaService> mockedService =
                     mockConstruction(CorsoLaureaService.class,
                             (mockService, context) -> when(mockService.trovaTutti())
                                     .thenReturn(List.of(mock(CorsoLaurea.class))))) {

            servlet.doGet(request, response);

            // Verifica del flusso di forward
            verify(request).setAttribute(eq("corsi"), any());
            verify(dispatcher).forward(request, response);
            // Nessuna interazione con response.sendError: il forward deve avvenire
            verify(response, never()).sendError(anyInt());
        }
    }

    @Test
    void testDoGetError_withJndiListingCovered() throws Exception {
        // Copriamo comunque il blocco JNDI, poi facciamo fallire il service
        NamingEnumeration<NameClassPair> rootEnum = mock(NamingEnumeration.class);
        when(rootEnum.hasMore()).thenReturn(false); // niente elementi: loop entra e termina

        try (MockedConstruction<InitialContext> mockedInitial =
                     mockConstruction(InitialContext.class, (mockCtx, context) ->
                             when(mockCtx.list("java:global")).thenReturn(rootEnum));
             MockedConstruction<CorsoLaureaService> mockedService =
                     mockConstruction(CorsoLaureaService.class,
                             (mockService, context) -> when(mockService.trovaTutti())
                                     .thenThrow(new RuntimeException("DB error")))) {

            servlet.doGet(request, response);

            // Verifica che sendError sia stato chiamato con errore 500
            verify(response).sendError(eq(HttpServletResponse.SC_INTERNAL_SERVER_ERROR), anyString());
            // Il forward non deve essere chiamato in caso di errore
            verify(dispatcher, never()).forward(request, response);
        }
    }

    @Test
    void testListJndiCatchBranchCovered() throws Exception {
        // Mock Context e NamingEnumeration
        Context ctx = mock(Context.class);
        NamingEnumeration<NameClassPair> rootEnum = mock(NamingEnumeration.class);

        // Simuliamo un elemento che porta a ricorsione
        when(rootEnum.hasMore()).thenReturn(true, false);
        NameClassPair subctx = new NameClassPair("subctx", "javax.naming.Context");
        when(rootEnum.next()).thenReturn(subctx);

        // Prima chiamata: java:global → restituisce l'enumerazione
        when(ctx.list("java:global")).thenReturn(rootEnum);
        // Ricorsione su java:global/subctx → lancia eccezione
        when(ctx.list("java:global/subctx")).thenThrow(new NamingException("not a context"));

        // Reflection per invocare il metodo privato
        Method listJNDIMethod = IndexServlet.class.getDeclaredMethod("listJNDI", Context.class, String.class);
        listJNDIMethod.setAccessible(true);

        // Invocazione: deve passare nel catch e stampare stacktrace
        listJNDIMethod.invoke(servlet, ctx, "java:global");

        // Verifica che la ricorsione sia stata tentata e abbia lanciato eccezione
        verify(ctx).list("java:global");
        verify(ctx).list("java:global/subctx");
    }

    @Test
    void testListJndiRecursiveCallAndCatchCovered() throws Exception {
        // Mock Context e NamingEnumeration
        Context ctx = mock(Context.class);
        NamingEnumeration<NameClassPair> rootEnum = mock(NamingEnumeration.class);

        // Simuliamo un elemento che porta a ricorsione
        when(rootEnum.hasMore()).thenReturn(true, false);
        NameClassPair subctx = new NameClassPair("subctx", "javax.naming.Context");
        when(rootEnum.next()).thenReturn(subctx);

        // Prima chiamata: java:global → restituisce l'enumerazione
        when(ctx.list("java:global")).thenReturn(rootEnum);
        // Ricorsione su java:global/subctx → lancia eccezione
        when(ctx.list("java:global/subctx")).thenThrow(new NamingException("not a context"));

        // Reflection per invocare il metodo privato
        Method listJNDIMethod = IndexServlet.class.getDeclaredMethod("listJNDI", Context.class, String.class);
        listJNDIMethod.setAccessible(true);

        // Invocazione: deve passare nel catch e stampare stacktrace
        listJNDIMethod.invoke(servlet, ctx, "java:global");

        // Verifica che la ricorsione sia stata tentata e abbia lanciato eccezione
        verify(ctx).list("java:global");
        verify(ctx).list("java:global/subctx");
    }

    @Test
    void testPrivateListJndi_viaReflection_directCoverage() throws Exception {
        // Invocazione diretta del metodo privato listJNDI via reflection per coprire rami e ricorsione

        // Mock di Context e NamingEnumeration per simulare elementi e ricorsione
        Context ctx = mock(Context.class);
        NamingEnumeration<NameClassPair> rootEnum = mock(NamingEnumeration.class);
        when(rootEnum.hasMore()).thenReturn(true, false);
        NameClassPair subctx = new NameClassPair("subctx", "javax.naming.Context");
        when(rootEnum.next()).thenReturn(subctx);
        when(ctx.list("java:global")).thenReturn(rootEnum);
        // Alla ricorsione su "java:global/subctx" lanciamo NamingException per arrivare al catch interno
        when(ctx.list("java:global/subctx")).thenThrow(new NamingException("not a context"));

        // Reflection per recuperare e invocare il metodo privato
        Method listJNDIMethod = IndexServlet.class.getDeclaredMethod("listJNDI", Context.class, String.class);
        listJNDIMethod.setAccessible(true);

        // Chiamata: non deve lanciare eccezioni, il catch interno gestisce la ricorsione non contestuale
        listJNDIMethod.invoke(servlet, ctx, "java:global");

        // Nessuna asserzione necessaria: l'obiettivo è coprire il ciclo e la ricorsione con catch
        verify(ctx).list("java:global");
        verify(ctx).list("java:global/subctx");
    }
}
